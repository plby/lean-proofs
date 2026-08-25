/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate423 : CompactCertificate where
  left := 294
  right := 295
  center := 589 / 2
  grid := fun i =>
    match i.val with
    | 0 => 94
    | 1 => 69
    | 2 => 112
    | 3 => 20
    | 4 => 54
    | 5 => 147
    | 6 => 108
    | 7 => 186
    | 8 => 137
    | 9 => 210
    | 10 => 121
    | 11 => 215
    | 12 => 201
    | 13 => 143
    | 14 => 162
    | 15 => 135
    | 16 => 120
    | 17 => 173
    | 18 => 96
    | 19 => 81
    | 20 => 51
    | 21 => 27
    | 22 => 74
    | 23 => 101
    | 24 => 43
    | 25 => 174
    | _ => 116
  point := fun i =>
    match i.val with
    | 0 => 589 / 2
    | 1 => 867709468313689 / 4000000000000
    | 2 => 280599413836537 / 800000000000
    | 3 => 253195458755723 / 4000000000000
    | 4 => 680118617105231 / 4000000000000
    | 5 => 1846654347353427 / 4000000000000
    | 6 => 1360237234211051 / 4000000000000
    | 7 => 2330789685321623 / 4000000000000
    | 8 => 1716849132937157 / 4000000000000
    | 9 => 2634088077494411 / 4000000000000
    | 10 => 1520791460610419 / 4000000000000
    | 11 => 2698671134193871 / 4000000000000
    | 12 => 2521448635976299 / 4000000000000
    | 13 => 1799424722885467 / 4000000000000
    | 14 => 2040355851315693 / 4000000000000
    | 15 => 1701035991036317 / 4000000000000
    | 16 => 1502916885326657 / 4000000000000
    | 17 => 435603892367043 / 800000000000
    | 18 => 1204903290864121 / 4000000000000
    | 19 => 1021409863604081 / 4000000000000
    | 20 => 639150867062843 / 4000000000000
    | 21 => 343737462026181 / 4000000000000
    | 22 => 933314075861543 / 4000000000000
    | 23 => 1274360579114311 / 4000000000000
    | 24 => 538849132937157 / 4000000000000
    | 25 => 2190391809380197 / 4000000000000
    | _ => 1463080217008523 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-1149945775 / 1000000000000) (-1149945773 / 1000000000000), orderedInterval (46481816351 / 1000000000000) (46481816353 / 1000000000000))
    | 1 => (orderedInterval (-43821027650 / 1000000000000) (-43821027649 / 1000000000000), orderedInterval (-31749100059 / 1000000000000) (-31749100058 / 1000000000000))
    | 2 => (orderedInterval (-13565923598 / 1000000000000) (-13565923470 / 1000000000000), orderedInterval (40404920937 / 1000000000000) (40404921064 / 1000000000000))
    | 3 => (orderedInterval (95182535620 / 1000000000000) (95182535621 / 1000000000000), orderedInterval (30829809416 / 1000000000000) (30829809417 / 1000000000000))
    | 4 => (orderedInterval (56299923032 / 1000000000000) (56299923033 / 1000000000000), orderedInterval (23802682020 / 1000000000000) (23802682021 / 1000000000000))
    | 5 => (orderedInterval (-22015192589 / 1000000000000) (-22015192588 / 1000000000000), orderedInterval (-29881014676 / 1000000000000) (-29881014675 / 1000000000000))
    | 6 => (orderedInterval (43260193750 / 1000000000000) (43260193893 / 1000000000000), orderedInterval (735231559 / 1000000000000) (735231702 / 1000000000000))
    | 7 => (orderedInterval (-24911503478 / 1000000000000) (-24911488687 / 1000000000000), orderedInterval (21745928188 / 1000000000000) (21745942979 / 1000000000000))
    | 8 => (orderedInterval (15026040302 / 1000000000000) (15026040512 / 1000000000000), orderedInterval (-35478003903 / 1000000000000) (-35478003692 / 1000000000000))
    | 9 => (orderedInterval (-12883183322 / 1000000000000) (-12883183262 / 1000000000000), orderedInterval (28307556820 / 1000000000000) (28307556880 / 1000000000000))
    | 10 => (orderedInterval (-30748386544 / 1000000000000) (-30748386543 / 1000000000000), orderedInterval (-26959189560 / 1000000000000) (-26959189559 / 1000000000000))
    | 11 => (orderedInterval (-324866423 / 1000000000000) (-324866422 / 1000000000000), orderedInterval (-30716196872 / 1000000000000) (-30716196871 / 1000000000000))
    | 12 => (orderedInterval (9778192831 / 1000000000000) (9778192844 / 1000000000000), orderedInterval (-30245385144 / 1000000000000) (-30245385131 / 1000000000000))
    | 13 => (orderedInterval (-37029276466 / 1000000000000) (-37029276433 / 1000000000000), orderedInterval (-6591697476 / 1000000000000) (-6591697443 / 1000000000000))
    | 14 => (orderedInterval (32996646286 / 1000000000000) (32996673984 / 1000000000000), orderedInterval (-12652829173 / 1000000000000) (-12652801475 / 1000000000000))
    | 15 => (orderedInterval (-36234212844 / 1000000000000) (-36234195521 / 1000000000000), orderedInterval (13610873972 / 1000000000000) (13610891295 / 1000000000000))
    | 16 => (orderedInterval (-18892237822 / 1000000000000) (-18892237040 / 1000000000000), orderedInterval (36596196182 / 1000000000000) (36596196964 / 1000000000000))
    | 17 => (orderedInterval (-33341106823 / 1000000000000) (-33341098468 / 1000000000000), orderedInterval (7616275366 / 1000000000000) (7616283721 / 1000000000000))
    | 18 => (orderedInterval (18657852101 / 1000000000000) (18657852102 / 1000000000000), orderedInterval (41984703226 / 1000000000000) (41984703227 / 1000000000000))
    | 19 => (orderedInterval (-49693429506 / 1000000000000) (-49693429128 / 1000000000000), orderedInterval (4961509726 / 1000000000000) (4961510105 / 1000000000000))
    | 20 => (orderedInterval (-21709368749 / 1000000000000) (-21709368748 / 1000000000000), orderedInterval (-59201604273 / 1000000000000) (-59201604272 / 1000000000000))
    | 21 => (orderedInterval (-81577938229 / 1000000000000) (-81577936152 / 1000000000000), orderedInterval (27918207588 / 1000000000000) (27918209665 / 1000000000000))
    | 22 => (orderedInterval (52124896881 / 1000000000000) (52124897094 / 1000000000000), orderedInterval (-3490403535 / 1000000000000) (-3490403323 / 1000000000000))
    | 23 => (orderedInterval (-39154246303 / 1000000000000) (-39154206022 / 1000000000000), orderedInterval (21629595578 / 1000000000000) (21629635859 / 1000000000000))
    | 24 => (orderedInterval (-27292861930 / 1000000000000) (-27292861929 / 1000000000000), orderedInterval (-62993040736 / 1000000000000) (-62993040735 / 1000000000000))
    | 25 => (orderedInterval (33574455892 / 1000000000000) (33574461044 / 1000000000000), orderedInterval (-5973984745 / 1000000000000) (-5973979593 / 1000000000000))
    | _ => (orderedInterval (35356351213 / 1000000000000) (35356432112 / 1000000000000), orderedInterval (-22193721189 / 1000000000000) (-22193640290 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1660189086 / 1000000000000) (-1660189057 / 1000000000000)
      | 1 => orderedInterval (2587997582 / 1000000000000) (2587997618 / 1000000000000)
      | 2 => orderedInterval (1131519721 / 1000000000000) (1131520200 / 1000000000000)
      | 3 => orderedInterval (-35198035 / 1000000000000) (-35197907 / 1000000000000)
      | 4 => orderedInterval (-3845103259 / 1000000000000) (-3845103080 / 1000000000000)
      | 5 => orderedInterval (-190944832 / 1000000000000) (-190944345 / 1000000000000)
      | 6 => orderedInterval (-877358053 / 1000000000000) (-877357957 / 1000000000000)
      | 7 => orderedInterval (3324529876 / 1000000000000) (3324533042 / 1000000000000)
      | _ => orderedInterval (-9531355720 / 1000000000000) (-9531340040 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (21029717633 / 1000000000000) (21029717667 / 1000000000000)
      | 1 => orderedInterval (3759852477 / 1000000000000) (3759852518 / 1000000000000)
      | 2 => orderedInterval (-2576756108 / 1000000000000) (-2576755169 / 1000000000000)
      | 3 => orderedInterval (-23829079944 / 1000000000000) (-23829079678 / 1000000000000)
      | 4 => orderedInterval (327485247 / 1000000000000) (327485553 / 1000000000000)
      | 5 => orderedInterval (-2084414279 / 1000000000000) (-2084413496 / 1000000000000)
      | 6 => orderedInterval (-8155555739 / 1000000000000) (-8155555651 / 1000000000000)
      | 7 => orderedInterval (-1880955730 / 1000000000000) (-1880952343 / 1000000000000)
      | _ => orderedInterval (5902361934 / 1000000000000) (5902381680 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (1735137122 / 1000000000000) (1735137160 / 1000000000000)
      | 1 => orderedInterval (-4496264553 / 1000000000000) (-4496264497 / 1000000000000)
      | 2 => orderedInterval (-3770672811 / 1000000000000) (-3770670959 / 1000000000000)
      | 3 => orderedInterval (-7325643079 / 1000000000000) (-7325642506 / 1000000000000)
      | 4 => orderedInterval (9478981339 / 1000000000000) (9478981863 / 1000000000000)
      | 5 => orderedInterval (2037985763 / 1000000000000) (2037987048 / 1000000000000)
      | 6 => orderedInterval (1242237845 / 1000000000000) (1242237927 / 1000000000000)
      | 7 => orderedInterval (-2891300609 / 1000000000000) (-2891296946 / 1000000000000)
      | _ => orderedInterval (19696706522 / 1000000000000) (19696731622 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-22316776447 / 1000000000000) (-22316776403 / 1000000000000)
      | 1 => orderedInterval (-8331811895 / 1000000000000) (-8331811811 / 1000000000000)
      | 2 => orderedInterval (7862577059 / 1000000000000) (7862580708 / 1000000000000)
      | 3 => orderedInterval (113056983099 / 1000000000000) (113056984357 / 1000000000000)
      | 4 => orderedInterval (-3497783636 / 1000000000000) (-3497782732 / 1000000000000)
      | 5 => orderedInterval (2636416720 / 1000000000000) (2636418865 / 1000000000000)
      | 6 => orderedInterval (7670150971 / 1000000000000) (7670151049 / 1000000000000)
      | 7 => orderedInterval (2081865232 / 1000000000000) (2081869189 / 1000000000000)
      | _ => orderedInterval (-11134725138 / 1000000000000) (-11134693016 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2026174072 / 1000000000000) (-2026174020 / 1000000000000)
      | 1 => orderedInterval (9733996167 / 1000000000000) (9733996296 / 1000000000000)
      | 2 => orderedInterval (13361112652 / 1000000000000) (13361119863 / 1000000000000)
      | 3 => orderedInterval (48861434927 / 1000000000000) (48861437721 / 1000000000000)
      | 4 => orderedInterval (-24248564478 / 1000000000000) (-24248562912 / 1000000000000)
      | 5 => orderedInterval (-8948575955 / 1000000000000) (-8948572304 / 1000000000000)
      | 6 => orderedInterval (-1788810323 / 1000000000000) (-1788810247 / 1000000000000)
      | 7 => orderedInterval (3640540406 / 1000000000000) (3640544698 / 1000000000000)
      | _ => orderedInterval (-48386693474 / 1000000000000) (-48386651708 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9096101806 / 1000000000000) (-9096081526 / 1000000000000)
    | 1 => orderedInterval (-7507344509 / 1000000000000) (-7507318919 / 1000000000000)
    | 2 => orderedInterval (15707167539 / 1000000000000) (15707200712 / 1000000000000)
    | 3 => orderedInterval (88026895965 / 1000000000000) (88026940206 / 1000000000000)
    | _ => orderedInterval (-9801734150 / 1000000000000) (-9801672613 / 1000000000000)

theorem compactCertificate423_stateChecks0 :
    compactCertificate423.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (589 / 2)) (orderedInterval (-1149945775 / 1000000000000) (-1149945773 / 1000000000000), orderedInterval (46481816351 / 1000000000000) (46481816353 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (867709468313689 / 4000000000000)) (orderedInterval (-43821027650 / 1000000000000) (-43821027649 / 1000000000000), orderedInterval (-31749100059 / 1000000000000) (-31749100058 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (280599413836537 / 800000000000)) (orderedInterval (-13565923598 / 1000000000000) (-13565923470 / 1000000000000), orderedInterval (40404920937 / 1000000000000) (40404921064 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_stateChecks1 :
    compactCertificate423.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (253195458755723 / 4000000000000)) (orderedInterval (95182535620 / 1000000000000) (95182535621 / 1000000000000), orderedInterval (30829809416 / 1000000000000) (30829809417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (680118617105231 / 4000000000000)) (orderedInterval (56299923032 / 1000000000000) (56299923033 / 1000000000000), orderedInterval (23802682020 / 1000000000000) (23802682021 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1846654347353427 / 4000000000000)) (orderedInterval (-22015192589 / 1000000000000) (-22015192588 / 1000000000000), orderedInterval (-29881014676 / 1000000000000) (-29881014675 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_stateChecks2 :
    compactCertificate423.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1360237234211051 / 4000000000000)) (orderedInterval (43260193750 / 1000000000000) (43260193893 / 1000000000000), orderedInterval (735231559 / 1000000000000) (735231702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2330789685321623 / 4000000000000)) (orderedInterval (-24911503478 / 1000000000000) (-24911488687 / 1000000000000), orderedInterval (21745928188 / 1000000000000) (21745942979 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1716849132937157 / 4000000000000)) (orderedInterval (15026040302 / 1000000000000) (15026040512 / 1000000000000), orderedInterval (-35478003903 / 1000000000000) (-35478003692 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_stateChecks3 :
    compactCertificate423.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2634088077494411 / 4000000000000)) (orderedInterval (-12883183322 / 1000000000000) (-12883183262 / 1000000000000), orderedInterval (28307556820 / 1000000000000) (28307556880 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1520791460610419 / 4000000000000)) (orderedInterval (-30748386544 / 1000000000000) (-30748386543 / 1000000000000), orderedInterval (-26959189560 / 1000000000000) (-26959189559 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2698671134193871 / 4000000000000)) (orderedInterval (-324866423 / 1000000000000) (-324866422 / 1000000000000), orderedInterval (-30716196872 / 1000000000000) (-30716196871 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_stateChecks4 :
    compactCertificate423.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2521448635976299 / 4000000000000)) (orderedInterval (9778192831 / 1000000000000) (9778192844 / 1000000000000), orderedInterval (-30245385144 / 1000000000000) (-30245385131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1799424722885467 / 4000000000000)) (orderedInterval (-37029276466 / 1000000000000) (-37029276433 / 1000000000000), orderedInterval (-6591697476 / 1000000000000) (-6591697443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2040355851315693 / 4000000000000)) (orderedInterval (32996646286 / 1000000000000) (32996673984 / 1000000000000), orderedInterval (-12652829173 / 1000000000000) (-12652801475 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_stateChecks5 :
    compactCertificate423.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1701035991036317 / 4000000000000)) (orderedInterval (-36234212844 / 1000000000000) (-36234195521 / 1000000000000), orderedInterval (13610873972 / 1000000000000) (13610891295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1502916885326657 / 4000000000000)) (orderedInterval (-18892237822 / 1000000000000) (-18892237040 / 1000000000000), orderedInterval (36596196182 / 1000000000000) (36596196964 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (435603892367043 / 800000000000)) (orderedInterval (-33341106823 / 1000000000000) (-33341098468 / 1000000000000), orderedInterval (7616275366 / 1000000000000) (7616283721 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_stateChecks6 :
    compactCertificate423.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1204903290864121 / 4000000000000)) (orderedInterval (18657852101 / 1000000000000) (18657852102 / 1000000000000), orderedInterval (41984703226 / 1000000000000) (41984703227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1021409863604081 / 4000000000000)) (orderedInterval (-49693429506 / 1000000000000) (-49693429128 / 1000000000000), orderedInterval (4961509726 / 1000000000000) (4961510105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (639150867062843 / 4000000000000)) (orderedInterval (-21709368749 / 1000000000000) (-21709368748 / 1000000000000), orderedInterval (-59201604273 / 1000000000000) (-59201604272 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_stateChecks7 :
    compactCertificate423.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (343737462026181 / 4000000000000)) (orderedInterval (-81577938229 / 1000000000000) (-81577936152 / 1000000000000), orderedInterval (27918207588 / 1000000000000) (27918209665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (933314075861543 / 4000000000000)) (orderedInterval (52124896881 / 1000000000000) (52124897094 / 1000000000000), orderedInterval (-3490403535 / 1000000000000) (-3490403323 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1274360579114311 / 4000000000000)) (orderedInterval (-39154246303 / 1000000000000) (-39154206022 / 1000000000000), orderedInterval (21629595578 / 1000000000000) (21629635859 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_stateChecks8 :
    compactCertificate423.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (538849132937157 / 4000000000000)) (orderedInterval (-27292861930 / 1000000000000) (-27292861929 / 1000000000000), orderedInterval (-62993040736 / 1000000000000) (-62993040735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2190391809380197 / 4000000000000)) (orderedInterval (33574455892 / 1000000000000) (33574461044 / 1000000000000), orderedInterval (-5973984745 / 1000000000000) (-5973979593 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1463080217008523 / 4000000000000)) (orderedInterval (35356351213 / 1000000000000) (35356432112 / 1000000000000), orderedInterval (-22193721189 / 1000000000000) (-22193640290 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_states : ∀ j,
    BesselStateValid (compactCertificate423.point j) (compactCertificate423.state j) :=
  compactCertificate423.statesValid_of_checks3 compactCertificate423_stateChecks0
    compactCertificate423_stateChecks1 compactCertificate423_stateChecks2
    compactCertificate423_stateChecks3 compactCertificate423_stateChecks4
    compactCertificate423_stateChecks5 compactCertificate423_stateChecks6
    compactCertificate423_stateChecks7 compactCertificate423_stateChecks8

theorem compactCertificate423_chunkChecks0_0 :
    compactCertificate423.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (589 / 2) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1149945775 / 1000000000000) (-1149945773 / 1000000000000), orderedInterval (46481816351 / 1000000000000) (46481816353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (867709468313689 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43821027650 / 1000000000000) (-43821027649 / 1000000000000), orderedInterval (-31749100059 / 1000000000000) (-31749100058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (280599413836537 / 800000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13565923598 / 1000000000000) (-13565923470 / 1000000000000), orderedInterval (40404920937 / 1000000000000) (40404921064 / 1000000000000)))) (orderedInterval (-1660189086 / 1000000000000) (-1660189057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (253195458755723 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95182535620 / 1000000000000) (95182535621 / 1000000000000), orderedInterval (30829809416 / 1000000000000) (30829809417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (680118617105231 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56299923032 / 1000000000000) (56299923033 / 1000000000000), orderedInterval (23802682020 / 1000000000000) (23802682021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1846654347353427 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22015192589 / 1000000000000) (-22015192588 / 1000000000000), orderedInterval (-29881014676 / 1000000000000) (-29881014675 / 1000000000000)))) (orderedInterval (2587997582 / 1000000000000) (2587997618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1360237234211051 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43260193750 / 1000000000000) (43260193893 / 1000000000000), orderedInterval (735231559 / 1000000000000) (735231702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2330789685321623 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24911503478 / 1000000000000) (-24911488687 / 1000000000000), orderedInterval (21745928188 / 1000000000000) (21745942979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1716849132937157 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15026040302 / 1000000000000) (15026040512 / 1000000000000), orderedInterval (-35478003903 / 1000000000000) (-35478003692 / 1000000000000)))) (orderedInterval (1131519721 / 1000000000000) (1131520200 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks0_1 :
    compactCertificate423.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2634088077494411 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12883183322 / 1000000000000) (-12883183262 / 1000000000000), orderedInterval (28307556820 / 1000000000000) (28307556880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1520791460610419 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30748386544 / 1000000000000) (-30748386543 / 1000000000000), orderedInterval (-26959189560 / 1000000000000) (-26959189559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2698671134193871 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-324866423 / 1000000000000) (-324866422 / 1000000000000), orderedInterval (-30716196872 / 1000000000000) (-30716196871 / 1000000000000)))) (orderedInterval (-35198035 / 1000000000000) (-35197907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2521448635976299 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9778192831 / 1000000000000) (9778192844 / 1000000000000), orderedInterval (-30245385144 / 1000000000000) (-30245385131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1799424722885467 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37029276466 / 1000000000000) (-37029276433 / 1000000000000), orderedInterval (-6591697476 / 1000000000000) (-6591697443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2040355851315693 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32996646286 / 1000000000000) (32996673984 / 1000000000000), orderedInterval (-12652829173 / 1000000000000) (-12652801475 / 1000000000000)))) (orderedInterval (-3845103259 / 1000000000000) (-3845103080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1701035991036317 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36234212844 / 1000000000000) (-36234195521 / 1000000000000), orderedInterval (13610873972 / 1000000000000) (13610891295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1502916885326657 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18892237822 / 1000000000000) (-18892237040 / 1000000000000), orderedInterval (36596196182 / 1000000000000) (36596196964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (435603892367043 / 800000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33341106823 / 1000000000000) (-33341098468 / 1000000000000), orderedInterval (7616275366 / 1000000000000) (7616283721 / 1000000000000)))) (orderedInterval (-190944832 / 1000000000000) (-190944345 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks0_2 :
    compactCertificate423.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1204903290864121 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18657852101 / 1000000000000) (18657852102 / 1000000000000), orderedInterval (41984703226 / 1000000000000) (41984703227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1021409863604081 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49693429506 / 1000000000000) (-49693429128 / 1000000000000), orderedInterval (4961509726 / 1000000000000) (4961510105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (639150867062843 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-21709368749 / 1000000000000) (-21709368748 / 1000000000000), orderedInterval (-59201604273 / 1000000000000) (-59201604272 / 1000000000000)))) (orderedInterval (-877358053 / 1000000000000) (-877357957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (343737462026181 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81577938229 / 1000000000000) (-81577936152 / 1000000000000), orderedInterval (27918207588 / 1000000000000) (27918209665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (933314075861543 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52124896881 / 1000000000000) (52124897094 / 1000000000000), orderedInterval (-3490403535 / 1000000000000) (-3490403323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1274360579114311 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39154246303 / 1000000000000) (-39154206022 / 1000000000000), orderedInterval (21629595578 / 1000000000000) (21629635859 / 1000000000000)))) (orderedInterval (3324529876 / 1000000000000) (3324533042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (538849132937157 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-27292861930 / 1000000000000) (-27292861929 / 1000000000000), orderedInterval (-62993040736 / 1000000000000) (-62993040735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2190391809380197 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33574455892 / 1000000000000) (33574461044 / 1000000000000), orderedInterval (-5973984745 / 1000000000000) (-5973979593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1463080217008523 / 4000000000000) 0 (IntervalRat.scale (589 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35356351213 / 1000000000000) (35356432112 / 1000000000000), orderedInterval (-22193721189 / 1000000000000) (-22193640290 / 1000000000000)))) (orderedInterval (-9531355720 / 1000000000000) (-9531340040 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks0 :
    compactCertificate423.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate423.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate423_chunkChecks0_0
    compactCertificate423_chunkChecks0_1 compactCertificate423_chunkChecks0_2

theorem compactCertificate423_chunkChecks1_0 :
    compactCertificate423.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (589 / 2) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1149945775 / 1000000000000) (-1149945773 / 1000000000000), orderedInterval (46481816351 / 1000000000000) (46481816353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (867709468313689 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43821027650 / 1000000000000) (-43821027649 / 1000000000000), orderedInterval (-31749100059 / 1000000000000) (-31749100058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (280599413836537 / 800000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13565923598 / 1000000000000) (-13565923470 / 1000000000000), orderedInterval (40404920937 / 1000000000000) (40404921064 / 1000000000000)))) (orderedInterval (21029717633 / 1000000000000) (21029717667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (253195458755723 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95182535620 / 1000000000000) (95182535621 / 1000000000000), orderedInterval (30829809416 / 1000000000000) (30829809417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (680118617105231 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56299923032 / 1000000000000) (56299923033 / 1000000000000), orderedInterval (23802682020 / 1000000000000) (23802682021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1846654347353427 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22015192589 / 1000000000000) (-22015192588 / 1000000000000), orderedInterval (-29881014676 / 1000000000000) (-29881014675 / 1000000000000)))) (orderedInterval (3759852477 / 1000000000000) (3759852518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1360237234211051 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43260193750 / 1000000000000) (43260193893 / 1000000000000), orderedInterval (735231559 / 1000000000000) (735231702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2330789685321623 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24911503478 / 1000000000000) (-24911488687 / 1000000000000), orderedInterval (21745928188 / 1000000000000) (21745942979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1716849132937157 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15026040302 / 1000000000000) (15026040512 / 1000000000000), orderedInterval (-35478003903 / 1000000000000) (-35478003692 / 1000000000000)))) (orderedInterval (-2576756108 / 1000000000000) (-2576755169 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks1_1 :
    compactCertificate423.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2634088077494411 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12883183322 / 1000000000000) (-12883183262 / 1000000000000), orderedInterval (28307556820 / 1000000000000) (28307556880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1520791460610419 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30748386544 / 1000000000000) (-30748386543 / 1000000000000), orderedInterval (-26959189560 / 1000000000000) (-26959189559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2698671134193871 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-324866423 / 1000000000000) (-324866422 / 1000000000000), orderedInterval (-30716196872 / 1000000000000) (-30716196871 / 1000000000000)))) (orderedInterval (-23829079944 / 1000000000000) (-23829079678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2521448635976299 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9778192831 / 1000000000000) (9778192844 / 1000000000000), orderedInterval (-30245385144 / 1000000000000) (-30245385131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1799424722885467 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37029276466 / 1000000000000) (-37029276433 / 1000000000000), orderedInterval (-6591697476 / 1000000000000) (-6591697443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2040355851315693 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32996646286 / 1000000000000) (32996673984 / 1000000000000), orderedInterval (-12652829173 / 1000000000000) (-12652801475 / 1000000000000)))) (orderedInterval (327485247 / 1000000000000) (327485553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1701035991036317 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36234212844 / 1000000000000) (-36234195521 / 1000000000000), orderedInterval (13610873972 / 1000000000000) (13610891295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1502916885326657 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18892237822 / 1000000000000) (-18892237040 / 1000000000000), orderedInterval (36596196182 / 1000000000000) (36596196964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (435603892367043 / 800000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33341106823 / 1000000000000) (-33341098468 / 1000000000000), orderedInterval (7616275366 / 1000000000000) (7616283721 / 1000000000000)))) (orderedInterval (-2084414279 / 1000000000000) (-2084413496 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks1_2 :
    compactCertificate423.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1204903290864121 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18657852101 / 1000000000000) (18657852102 / 1000000000000), orderedInterval (41984703226 / 1000000000000) (41984703227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1021409863604081 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49693429506 / 1000000000000) (-49693429128 / 1000000000000), orderedInterval (4961509726 / 1000000000000) (4961510105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (639150867062843 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-21709368749 / 1000000000000) (-21709368748 / 1000000000000), orderedInterval (-59201604273 / 1000000000000) (-59201604272 / 1000000000000)))) (orderedInterval (-8155555739 / 1000000000000) (-8155555651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (343737462026181 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81577938229 / 1000000000000) (-81577936152 / 1000000000000), orderedInterval (27918207588 / 1000000000000) (27918209665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (933314075861543 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52124896881 / 1000000000000) (52124897094 / 1000000000000), orderedInterval (-3490403535 / 1000000000000) (-3490403323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1274360579114311 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39154246303 / 1000000000000) (-39154206022 / 1000000000000), orderedInterval (21629595578 / 1000000000000) (21629635859 / 1000000000000)))) (orderedInterval (-1880955730 / 1000000000000) (-1880952343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (538849132937157 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-27292861930 / 1000000000000) (-27292861929 / 1000000000000), orderedInterval (-62993040736 / 1000000000000) (-62993040735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2190391809380197 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33574455892 / 1000000000000) (33574461044 / 1000000000000), orderedInterval (-5973984745 / 1000000000000) (-5973979593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1463080217008523 / 4000000000000) 1 (IntervalRat.scale (589 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35356351213 / 1000000000000) (35356432112 / 1000000000000), orderedInterval (-22193721189 / 1000000000000) (-22193640290 / 1000000000000)))) (orderedInterval (5902361934 / 1000000000000) (5902381680 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks1 :
    compactCertificate423.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate423.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate423_chunkChecks1_0
    compactCertificate423_chunkChecks1_1 compactCertificate423_chunkChecks1_2

theorem compactCertificate423_chunkChecks2_0 :
    compactCertificate423.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (589 / 2) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1149945775 / 1000000000000) (-1149945773 / 1000000000000), orderedInterval (46481816351 / 1000000000000) (46481816353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (867709468313689 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43821027650 / 1000000000000) (-43821027649 / 1000000000000), orderedInterval (-31749100059 / 1000000000000) (-31749100058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (280599413836537 / 800000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13565923598 / 1000000000000) (-13565923470 / 1000000000000), orderedInterval (40404920937 / 1000000000000) (40404921064 / 1000000000000)))) (orderedInterval (1735137122 / 1000000000000) (1735137160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (253195458755723 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95182535620 / 1000000000000) (95182535621 / 1000000000000), orderedInterval (30829809416 / 1000000000000) (30829809417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (680118617105231 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56299923032 / 1000000000000) (56299923033 / 1000000000000), orderedInterval (23802682020 / 1000000000000) (23802682021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1846654347353427 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22015192589 / 1000000000000) (-22015192588 / 1000000000000), orderedInterval (-29881014676 / 1000000000000) (-29881014675 / 1000000000000)))) (orderedInterval (-4496264553 / 1000000000000) (-4496264497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1360237234211051 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43260193750 / 1000000000000) (43260193893 / 1000000000000), orderedInterval (735231559 / 1000000000000) (735231702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2330789685321623 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24911503478 / 1000000000000) (-24911488687 / 1000000000000), orderedInterval (21745928188 / 1000000000000) (21745942979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1716849132937157 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15026040302 / 1000000000000) (15026040512 / 1000000000000), orderedInterval (-35478003903 / 1000000000000) (-35478003692 / 1000000000000)))) (orderedInterval (-3770672811 / 1000000000000) (-3770670959 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks2_1 :
    compactCertificate423.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2634088077494411 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12883183322 / 1000000000000) (-12883183262 / 1000000000000), orderedInterval (28307556820 / 1000000000000) (28307556880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1520791460610419 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30748386544 / 1000000000000) (-30748386543 / 1000000000000), orderedInterval (-26959189560 / 1000000000000) (-26959189559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2698671134193871 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-324866423 / 1000000000000) (-324866422 / 1000000000000), orderedInterval (-30716196872 / 1000000000000) (-30716196871 / 1000000000000)))) (orderedInterval (-7325643079 / 1000000000000) (-7325642506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2521448635976299 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9778192831 / 1000000000000) (9778192844 / 1000000000000), orderedInterval (-30245385144 / 1000000000000) (-30245385131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1799424722885467 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37029276466 / 1000000000000) (-37029276433 / 1000000000000), orderedInterval (-6591697476 / 1000000000000) (-6591697443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2040355851315693 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32996646286 / 1000000000000) (32996673984 / 1000000000000), orderedInterval (-12652829173 / 1000000000000) (-12652801475 / 1000000000000)))) (orderedInterval (9478981339 / 1000000000000) (9478981863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1701035991036317 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36234212844 / 1000000000000) (-36234195521 / 1000000000000), orderedInterval (13610873972 / 1000000000000) (13610891295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1502916885326657 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18892237822 / 1000000000000) (-18892237040 / 1000000000000), orderedInterval (36596196182 / 1000000000000) (36596196964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (435603892367043 / 800000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33341106823 / 1000000000000) (-33341098468 / 1000000000000), orderedInterval (7616275366 / 1000000000000) (7616283721 / 1000000000000)))) (orderedInterval (2037985763 / 1000000000000) (2037987048 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks2_2 :
    compactCertificate423.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1204903290864121 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18657852101 / 1000000000000) (18657852102 / 1000000000000), orderedInterval (41984703226 / 1000000000000) (41984703227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1021409863604081 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49693429506 / 1000000000000) (-49693429128 / 1000000000000), orderedInterval (4961509726 / 1000000000000) (4961510105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (639150867062843 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-21709368749 / 1000000000000) (-21709368748 / 1000000000000), orderedInterval (-59201604273 / 1000000000000) (-59201604272 / 1000000000000)))) (orderedInterval (1242237845 / 1000000000000) (1242237927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (343737462026181 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81577938229 / 1000000000000) (-81577936152 / 1000000000000), orderedInterval (27918207588 / 1000000000000) (27918209665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (933314075861543 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52124896881 / 1000000000000) (52124897094 / 1000000000000), orderedInterval (-3490403535 / 1000000000000) (-3490403323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1274360579114311 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39154246303 / 1000000000000) (-39154206022 / 1000000000000), orderedInterval (21629595578 / 1000000000000) (21629635859 / 1000000000000)))) (orderedInterval (-2891300609 / 1000000000000) (-2891296946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (538849132937157 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-27292861930 / 1000000000000) (-27292861929 / 1000000000000), orderedInterval (-62993040736 / 1000000000000) (-62993040735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2190391809380197 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33574455892 / 1000000000000) (33574461044 / 1000000000000), orderedInterval (-5973984745 / 1000000000000) (-5973979593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1463080217008523 / 4000000000000) 2 (IntervalRat.scale (589 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35356351213 / 1000000000000) (35356432112 / 1000000000000), orderedInterval (-22193721189 / 1000000000000) (-22193640290 / 1000000000000)))) (orderedInterval (19696706522 / 1000000000000) (19696731622 / 1000000000000))) = true
  rfl'

theorem compactCertificate423_chunkChecks2 :
    compactCertificate423.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate423.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate423_chunkChecks2_0
    compactCertificate423_chunkChecks2_1 compactCertificate423_chunkChecks2_2

theorem compactCertificate423_chunkChecks3_0 :
    compactCertificate423.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (589 / 2) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1149945775 / 1000000000000) (-1149945773 / 1000000000000), orderedInterval (46481816351 / 1000000000000) (46481816353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (867709468313689 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43821027650 / 1000000000000) (-43821027649 / 1000000000000), orderedInterval (-31749100059 / 1000000000000) (-31749100058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (280599413836537 / 800000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13565923598 / 1000000000000) (-13565923470 / 1000000000000), orderedInterval (40404920937 / 1000000000000) (40404921064 / 1000000000000)))) (orderedInterval (-22316776447 / 1000000000000) (-22316776403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (253195458755723 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95182535620 / 1000000000000) (95182535621 / 1000000000000), orderedInterval (30829809416 / 1000000000000) (30829809417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (680118617105231 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56299923032 / 1000000000000) (56299923033 / 1000000000000), orderedInterval (23802682020 / 1000000000000) (23802682021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1846654347353427 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22015192589 / 1000000000000) (-22015192588 / 1000000000000), orderedInterval (-29881014676 / 1000000000000) (-29881014675 / 1000000000000)))) (orderedInterval (-8331811895 / 1000000000000) (-8331811811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1360237234211051 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43260193750 / 1000000000000) (43260193893 / 1000000000000), orderedInterval (735231559 / 1000000000000) (735231702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2330789685321623 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24911503478 / 1000000000000) (-24911488687 / 1000000000000), orderedInterval (21745928188 / 1000000000000) (21745942979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1716849132937157 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15026040302 / 1000000000000) (15026040512 / 1000000000000), orderedInterval (-35478003903 / 1000000000000) (-35478003692 / 1000000000000)))) (orderedInterval (7862577059 / 1000000000000) (7862580708 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate423_chunkChecks3_1 :
    compactCertificate423.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2634088077494411 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12883183322 / 1000000000000) (-12883183262 / 1000000000000), orderedInterval (28307556820 / 1000000000000) (28307556880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1520791460610419 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30748386544 / 1000000000000) (-30748386543 / 1000000000000), orderedInterval (-26959189560 / 1000000000000) (-26959189559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2698671134193871 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-324866423 / 1000000000000) (-324866422 / 1000000000000), orderedInterval (-30716196872 / 1000000000000) (-30716196871 / 1000000000000)))) (orderedInterval (113056983099 / 1000000000000) (113056984357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2521448635976299 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9778192831 / 1000000000000) (9778192844 / 1000000000000), orderedInterval (-30245385144 / 1000000000000) (-30245385131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1799424722885467 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37029276466 / 1000000000000) (-37029276433 / 1000000000000), orderedInterval (-6591697476 / 1000000000000) (-6591697443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2040355851315693 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32996646286 / 1000000000000) (32996673984 / 1000000000000), orderedInterval (-12652829173 / 1000000000000) (-12652801475 / 1000000000000)))) (orderedInterval (-3497783636 / 1000000000000) (-3497782732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1701035991036317 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36234212844 / 1000000000000) (-36234195521 / 1000000000000), orderedInterval (13610873972 / 1000000000000) (13610891295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1502916885326657 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18892237822 / 1000000000000) (-18892237040 / 1000000000000), orderedInterval (36596196182 / 1000000000000) (36596196964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (435603892367043 / 800000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33341106823 / 1000000000000) (-33341098468 / 1000000000000), orderedInterval (7616275366 / 1000000000000) (7616283721 / 1000000000000)))) (orderedInterval (2636416720 / 1000000000000) (2636418865 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate423_chunkChecks3_2 :
    compactCertificate423.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1204903290864121 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18657852101 / 1000000000000) (18657852102 / 1000000000000), orderedInterval (41984703226 / 1000000000000) (41984703227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1021409863604081 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49693429506 / 1000000000000) (-49693429128 / 1000000000000), orderedInterval (4961509726 / 1000000000000) (4961510105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (639150867062843 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-21709368749 / 1000000000000) (-21709368748 / 1000000000000), orderedInterval (-59201604273 / 1000000000000) (-59201604272 / 1000000000000)))) (orderedInterval (7670150971 / 1000000000000) (7670151049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (343737462026181 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81577938229 / 1000000000000) (-81577936152 / 1000000000000), orderedInterval (27918207588 / 1000000000000) (27918209665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (933314075861543 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52124896881 / 1000000000000) (52124897094 / 1000000000000), orderedInterval (-3490403535 / 1000000000000) (-3490403323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1274360579114311 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39154246303 / 1000000000000) (-39154206022 / 1000000000000), orderedInterval (21629595578 / 1000000000000) (21629635859 / 1000000000000)))) (orderedInterval (2081865232 / 1000000000000) (2081869189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (538849132937157 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-27292861930 / 1000000000000) (-27292861929 / 1000000000000), orderedInterval (-62993040736 / 1000000000000) (-62993040735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2190391809380197 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33574455892 / 1000000000000) (33574461044 / 1000000000000), orderedInterval (-5973984745 / 1000000000000) (-5973979593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1463080217008523 / 4000000000000) 3 (IntervalRat.scale (589 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35356351213 / 1000000000000) (35356432112 / 1000000000000), orderedInterval (-22193721189 / 1000000000000) (-22193640290 / 1000000000000)))) (orderedInterval (-11134725138 / 1000000000000) (-11134693016 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate423_chunkChecks3 :
    compactCertificate423.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate423.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate423_chunkChecks3_0
    compactCertificate423_chunkChecks3_1 compactCertificate423_chunkChecks3_2

theorem compactCertificate423_chunkChecks4_0 :
    compactCertificate423.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (589 / 2) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1149945775 / 1000000000000) (-1149945773 / 1000000000000), orderedInterval (46481816351 / 1000000000000) (46481816353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (867709468313689 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43821027650 / 1000000000000) (-43821027649 / 1000000000000), orderedInterval (-31749100059 / 1000000000000) (-31749100058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (280599413836537 / 800000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13565923598 / 1000000000000) (-13565923470 / 1000000000000), orderedInterval (40404920937 / 1000000000000) (40404921064 / 1000000000000)))) (orderedInterval (-2026174072 / 1000000000000) (-2026174020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (253195458755723 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (95182535620 / 1000000000000) (95182535621 / 1000000000000), orderedInterval (30829809416 / 1000000000000) (30829809417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (680118617105231 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56299923032 / 1000000000000) (56299923033 / 1000000000000), orderedInterval (23802682020 / 1000000000000) (23802682021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1846654347353427 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22015192589 / 1000000000000) (-22015192588 / 1000000000000), orderedInterval (-29881014676 / 1000000000000) (-29881014675 / 1000000000000)))) (orderedInterval (9733996167 / 1000000000000) (9733996296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1360237234211051 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43260193750 / 1000000000000) (43260193893 / 1000000000000), orderedInterval (735231559 / 1000000000000) (735231702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2330789685321623 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24911503478 / 1000000000000) (-24911488687 / 1000000000000), orderedInterval (21745928188 / 1000000000000) (21745942979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1716849132937157 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15026040302 / 1000000000000) (15026040512 / 1000000000000), orderedInterval (-35478003903 / 1000000000000) (-35478003692 / 1000000000000)))) (orderedInterval (13361112652 / 1000000000000) (13361119863 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate423_chunkChecks4_1 :
    compactCertificate423.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2634088077494411 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12883183322 / 1000000000000) (-12883183262 / 1000000000000), orderedInterval (28307556820 / 1000000000000) (28307556880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1520791460610419 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30748386544 / 1000000000000) (-30748386543 / 1000000000000), orderedInterval (-26959189560 / 1000000000000) (-26959189559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2698671134193871 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-324866423 / 1000000000000) (-324866422 / 1000000000000), orderedInterval (-30716196872 / 1000000000000) (-30716196871 / 1000000000000)))) (orderedInterval (48861434927 / 1000000000000) (48861437721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2521448635976299 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9778192831 / 1000000000000) (9778192844 / 1000000000000), orderedInterval (-30245385144 / 1000000000000) (-30245385131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1799424722885467 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37029276466 / 1000000000000) (-37029276433 / 1000000000000), orderedInterval (-6591697476 / 1000000000000) (-6591697443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2040355851315693 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32996646286 / 1000000000000) (32996673984 / 1000000000000), orderedInterval (-12652829173 / 1000000000000) (-12652801475 / 1000000000000)))) (orderedInterval (-24248564478 / 1000000000000) (-24248562912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1701035991036317 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36234212844 / 1000000000000) (-36234195521 / 1000000000000), orderedInterval (13610873972 / 1000000000000) (13610891295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1502916885326657 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18892237822 / 1000000000000) (-18892237040 / 1000000000000), orderedInterval (36596196182 / 1000000000000) (36596196964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (435603892367043 / 800000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33341106823 / 1000000000000) (-33341098468 / 1000000000000), orderedInterval (7616275366 / 1000000000000) (7616283721 / 1000000000000)))) (orderedInterval (-8948575955 / 1000000000000) (-8948572304 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate423_chunkChecks4_2 :
    compactCertificate423.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1204903290864121 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18657852101 / 1000000000000) (18657852102 / 1000000000000), orderedInterval (41984703226 / 1000000000000) (41984703227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1021409863604081 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49693429506 / 1000000000000) (-49693429128 / 1000000000000), orderedInterval (4961509726 / 1000000000000) (4961510105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (639150867062843 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-21709368749 / 1000000000000) (-21709368748 / 1000000000000), orderedInterval (-59201604273 / 1000000000000) (-59201604272 / 1000000000000)))) (orderedInterval (-1788810323 / 1000000000000) (-1788810247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (343737462026181 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81577938229 / 1000000000000) (-81577936152 / 1000000000000), orderedInterval (27918207588 / 1000000000000) (27918209665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (933314075861543 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52124896881 / 1000000000000) (52124897094 / 1000000000000), orderedInterval (-3490403535 / 1000000000000) (-3490403323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1274360579114311 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39154246303 / 1000000000000) (-39154206022 / 1000000000000), orderedInterval (21629595578 / 1000000000000) (21629635859 / 1000000000000)))) (orderedInterval (3640540406 / 1000000000000) (3640544698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (538849132937157 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-27292861930 / 1000000000000) (-27292861929 / 1000000000000), orderedInterval (-62993040736 / 1000000000000) (-62993040735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2190391809380197 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33574455892 / 1000000000000) (33574461044 / 1000000000000), orderedInterval (-5973984745 / 1000000000000) (-5973979593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1463080217008523 / 4000000000000) 4 (IntervalRat.scale (589 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35356351213 / 1000000000000) (35356432112 / 1000000000000), orderedInterval (-22193721189 / 1000000000000) (-22193640290 / 1000000000000)))) (orderedInterval (-48386693474 / 1000000000000) (-48386651708 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate423_chunkChecks4 :
    compactCertificate423.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate423.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate423_chunkChecks4_0
    compactCertificate423_chunkChecks4_1 compactCertificate423_chunkChecks4_2

theorem compactCertificate423_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate423.chunkCheck r b = true :=
  compactCertificate423.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate423_chunkChecks0
    · exact compactCertificate423_chunkChecks1
    · exact compactCertificate423_chunkChecks2
    · exact compactCertificate423_chunkChecks3
    · exact compactCertificate423_chunkChecks4)

theorem compactCertificate423_coefficient0 :
    compactCertificate423.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate423_coefficient1 :
    compactCertificate423.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate423_coefficient2 :
    compactCertificate423.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate423_coefficient3 :
    compactCertificate423.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate423_coefficient4 :
    compactCertificate423.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate423_coefficients : ∀ r : Fin 5,
    compactCertificate423.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate423_coefficient0
  · exact compactCertificate423_coefficient1
  · exact compactCertificate423_coefficient2
  · exact compactCertificate423_coefficient3
  · exact compactCertificate423_coefficient4

theorem compactCertificate423_lower : (1 : ℚ) ≤ compactCertificate423.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate423, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate423_proves {t : ℝ} (ht : t ∈ compactCertificate423.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate423.proves compactCertificate423_states compactCertificate423_chunks
    compactCertificate423_coefficients compactCertificate423_lower ht

end Erdos232
