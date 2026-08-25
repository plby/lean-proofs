/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate541 : CompactCertificate where
  left := 412
  right := 413
  center := 825 / 2
  grid := fun i =>
    match i.val with
    | 0 => 131
    | 1 => 97
    | 2 => 156
    | 3 => 28
    | 4 => 76
    | 5 => 206
    | 6 => 152
    | 7 => 260
    | 8 => 191
    | 9 => 294
    | 10 => 170
    | 11 => 301
    | 12 => 281
    | 13 => 201
    | 14 => 228
    | 15 => 190
    | 16 => 168
    | 17 => 243
    | 18 => 134
    | 19 => 114
    | 20 => 71
    | 21 => 38
    | 22 => 104
    | 23 => 142
    | 24 => 60
    | 25 => 244
    | _ => 163
  point := fun i =>
    match i.val with
    | 0 => 825 / 2
    | 1 => 48615301280733 / 160000000000
    | 2 => 15721189569789 / 32000000000
    | 3 => 14185823665431 / 160000000000
    | 4 => 38105117766507 / 160000000000
    | 5 => 103462807237119 / 160000000000
    | 6 => 76210235533047 / 160000000000
    | 7 => 130587537547731 / 160000000000
    | 8 => 96190189111929 / 160000000000
    | 9 => 147580486514967 / 160000000000
    | 10 => 85205633616543 / 160000000000
    | 11 => 151198892068587 / 160000000000
    | 12 => 141269617974903 / 160000000000
    | 13 => 100816665288999 / 160000000000
    | 14 => 114315353299521 / 160000000000
    | 15 => 95304223606449 / 160000000000
    | 16 => 84204171843429 / 160000000000
    | 17 => 24405651015471 / 32000000000
    | 18 => 67507315107837 / 160000000000
    | 19 => 57226698639957 / 160000000000
    | 20 => 35809810888071 / 160000000000
    | 21 => 19258635393657 / 160000000000
    | 22 => 52290941431971 / 160000000000
    | 23 => 71398810035267 / 160000000000
    | 24 => 30190189111929 / 160000000000
    | 25 => 122721442630809 / 160000000000
    | _ => 81972236267031 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-38747275493 / 1000000000000) (-38747273281 / 1000000000000), orderedInterval (6525260734 / 1000000000000) (6525262947 / 1000000000000))
    | 1 => (orderedInterval (4745831067 / 1000000000000) (4745831074 / 1000000000000), orderedInterval (-45534590379 / 1000000000000) (-45534590372 / 1000000000000))
    | 2 => (orderedInterval (32969858101 / 1000000000000) (32969897324 / 1000000000000), orderedInterval (-14483719960 / 1000000000000) (-14483680738 / 1000000000000))
    | 3 => (orderedInterval (84393282720 / 1000000000000) (84393282728 / 1000000000000), orderedInterval (7140543171 / 1000000000000) (7140543178 / 1000000000000))
    | 4 => (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))
    | 5 => (orderedInterval (8056144993 / 1000000000000) (8056144994 / 1000000000000), orderedInterval (30318662745 / 1000000000000) (30318662746 / 1000000000000))
    | 6 => (orderedInterval (-15006540963 / 1000000000000) (-15006540757 / 1000000000000), orderedInterval (33352805883 / 1000000000000) (33352806089 / 1000000000000))
    | 7 => (orderedInterval (3987510494 / 1000000000000) (3987510495 / 1000000000000), orderedInterval (27640036673 / 1000000000000) (27640036674 / 1000000000000))
    | 8 => (orderedInterval (-30468127953 / 1000000000000) (-30468088197 / 1000000000000), orderedInterval (11454630236 / 1000000000000) (11454669993 / 1000000000000))
    | 9 => (orderedInterval (-11779273873 / 1000000000000) (-11779273859 / 1000000000000), orderedInterval (23489203438 / 1000000000000) (23489203452 / 1000000000000))
    | 10 => (orderedInterval (-23577409701 / 1000000000000) (-23577402893 / 1000000000000), orderedInterval (25311597429 / 1000000000000) (25311604238 / 1000000000000))
    | 11 => (orderedInterval (-4108307698 / 1000000000000) (-4108307697 / 1000000000000), orderedInterval (-25625907568 / 1000000000000) (-25625907567 / 1000000000000))
    | 12 => (orderedInterval (-21570444902 / 1000000000000) (-21570444901 / 1000000000000), orderedInterval (-15979737562 / 1000000000000) (-15979737561 / 1000000000000))
    | 13 => (orderedInterval (17173143737 / 1000000000000) (17173144246 / 1000000000000), orderedInterval (-26761034687 / 1000000000000) (-26761034179 / 1000000000000))
    | 14 => (orderedInterval (-25543506319 / 1000000000000) (-25543466434 / 1000000000000), orderedInterval (15463462559 / 1000000000000) (15463502445 / 1000000000000))
    | 15 => (orderedInterval (-14689668788 / 1000000000000) (-14689668626 / 1000000000000), orderedInterval (29218374064 / 1000000000000) (29218374226 / 1000000000000))
    | 16 => (orderedInterval (-23098676131 / 1000000000000) (-23098670647 / 1000000000000), orderedInterval (26024253959 / 1000000000000) (26024259444 / 1000000000000))
    | 17 => (orderedInterval (-1582855443 / 1000000000000) (-1582855442 / 1000000000000), orderedInterval (-28847057630 / 1000000000000) (-28847057629 / 1000000000000))
    | 18 => (orderedInterval (38337893234 / 1000000000000) (38337895464 / 1000000000000), orderedInterval (-6295711763 / 1000000000000) (-6295709532 / 1000000000000))
    | 19 => (orderedInterval (12884324977 / 1000000000000) (12884324978 / 1000000000000), orderedInterval (40155604082 / 1000000000000) (40155604083 / 1000000000000))
    | 20 => (orderedInterval (-53312820131 / 1000000000000) (-53312820076 / 1000000000000), orderedInterval (-1358953076 / 1000000000000) (-1358953022 / 1000000000000))
    | 21 => (orderedInterval (71282636604 / 1000000000000) (71282637184 / 1000000000000), orderedInterval (-14709850364 / 1000000000000) (-14709849783 / 1000000000000))
    | 22 => (orderedInterval (33953856956 / 1000000000000) (33953856957 / 1000000000000), orderedInterval (28144977975 / 1000000000000) (28144977976 / 1000000000000))
    | 23 => (orderedInterval (30085224953 / 1000000000000) (30085224954 / 1000000000000), orderedInterval (22802702362 / 1000000000000) (22802702363 / 1000000000000))
    | 24 => (orderedInterval (48170303761 / 1000000000000) (48170303762 / 1000000000000), orderedInterval (32330535797 / 1000000000000) (32330535798 / 1000000000000))
    | 25 => (orderedInterval (27300198657 / 1000000000000) (27300198697 / 1000000000000), orderedInterval (9185572176 / 1000000000000) (9185572215 / 1000000000000))
    | _ => (orderedInterval (-30257053802 / 1000000000000) (-30257053801 / 1000000000000), orderedInterval (-18056821077 / 1000000000000) (-18056821076 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13379132796 / 1000000000000) (-13379129589 / 1000000000000)
      | 1 => orderedInterval (-1148837270 / 1000000000000) (-1148837220 / 1000000000000)
      | 2 => orderedInterval (-859345329 / 1000000000000) (-859344344 / 1000000000000)
      | 3 => orderedInterval (-237877526 / 1000000000000) (-237876855 / 1000000000000)
      | 4 => orderedInterval (2142619415 / 1000000000000) (2142619715 / 1000000000000)
      | 5 => orderedInterval (1111701345 / 1000000000000) (1111701701 / 1000000000000)
      | 6 => orderedInterval (-8594805313 / 1000000000000) (-8594804851 / 1000000000000)
      | 7 => orderedInterval (-4392246372 / 1000000000000) (-4392246311 / 1000000000000)
      | _ => orderedInterval (3745127569 / 1000000000000) (3745127687 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (1261596359 / 1000000000000) (1261600010 / 1000000000000)
      | 1 => orderedInterval (-2323700490 / 1000000000000) (-2323700433 / 1000000000000)
      | 2 => orderedInterval (-1283345706 / 1000000000000) (-1283344265 / 1000000000000)
      | 3 => orderedInterval (-15257108943 / 1000000000000) (-15257107947 / 1000000000000)
      | 4 => orderedInterval (-3383611589 / 1000000000000) (-3383611086 / 1000000000000)
      | 5 => orderedInterval (-2778448655 / 1000000000000) (-2778448194 / 1000000000000)
      | 6 => orderedInterval (-965062128 / 1000000000000) (-965061666 / 1000000000000)
      | 7 => orderedInterval (-2317159420 / 1000000000000) (-2317159372 / 1000000000000)
      | _ => orderedInterval (2906658028 / 1000000000000) (2906658194 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12586663254 / 1000000000000) (12586667442 / 1000000000000)
      | 1 => orderedInterval (1342161997 / 1000000000000) (1342162075 / 1000000000000)
      | 2 => orderedInterval (2048686117 / 1000000000000) (2048688234 / 1000000000000)
      | 3 => orderedInterval (-4451654008 / 1000000000000) (-4451652426 / 1000000000000)
      | 4 => orderedInterval (-5952893562 / 1000000000000) (-5952892710 / 1000000000000)
      | 5 => orderedInterval (-1652633200 / 1000000000000) (-1652632599 / 1000000000000)
      | 6 => orderedInterval (7474668571 / 1000000000000) (7474669037 / 1000000000000)
      | 7 => orderedInterval (3299564080 / 1000000000000) (3299564126 / 1000000000000)
      | _ => orderedInterval (-1141645874 / 1000000000000) (-1141645626 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-1011460203 / 1000000000000) (-1011455384 / 1000000000000)
      | 1 => orderedInterval (7943310452 / 1000000000000) (7943310569 / 1000000000000)
      | 2 => orderedInterval (5741648734 / 1000000000000) (5741651844 / 1000000000000)
      | 3 => orderedInterval (86437831561 / 1000000000000) (86437834270 / 1000000000000)
      | 4 => orderedInterval (6611643310 / 1000000000000) (6611644756 / 1000000000000)
      | 5 => orderedInterval (6749128368 / 1000000000000) (6749129158 / 1000000000000)
      | 6 => orderedInterval (393332278 / 1000000000000) (393332750 / 1000000000000)
      | 7 => orderedInterval (2515262442 / 1000000000000) (2515262488 / 1000000000000)
      | _ => orderedInterval (-1699806567 / 1000000000000) (-1699806181 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11447272515 / 1000000000000) (-11447266933 / 1000000000000)
      | 1 => orderedInterval (-3461296055 / 1000000000000) (-3461295875 / 1000000000000)
      | 2 => orderedInterval (-5235058837 / 1000000000000) (-5235054246 / 1000000000000)
      | 3 => orderedInterval (30968327575 / 1000000000000) (30968332581 / 1000000000000)
      | 4 => orderedInterval (18146661410 / 1000000000000) (18146663883 / 1000000000000)
      | 5 => orderedInterval (2258361693 / 1000000000000) (2258362744 / 1000000000000)
      | 6 => orderedInterval (-7273867390 / 1000000000000) (-7273866910 / 1000000000000)
      | 7 => orderedInterval (-3483085548 / 1000000000000) (-3483085500 / 1000000000000)
      | _ => orderedInterval (-13035143786 / 1000000000000) (-13035143160 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-21612796277 / 1000000000000) (-21612790067 / 1000000000000)
    | 1 => orderedInterval (-24140182544 / 1000000000000) (-24140174759 / 1000000000000)
    | 2 => orderedInterval (13552917375 / 1000000000000) (13552927553 / 1000000000000)
    | 3 => orderedInterval (113680890375 / 1000000000000) (113680904270 / 1000000000000)
    | _ => orderedInterval (7437626547 / 1000000000000) (7437646584 / 1000000000000)

theorem compactCertificate541_stateChecks0 :
    compactCertificate541.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (825 / 2)) (orderedInterval (-38747275493 / 1000000000000) (-38747273281 / 1000000000000), orderedInterval (6525260734 / 1000000000000) (6525262947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (48615301280733 / 160000000000)) (orderedInterval (4745831067 / 1000000000000) (4745831074 / 1000000000000), orderedInterval (-45534590379 / 1000000000000) (-45534590372 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (15721189569789 / 32000000000)) (orderedInterval (32969858101 / 1000000000000) (32969897324 / 1000000000000), orderedInterval (-14483719960 / 1000000000000) (-14483680738 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_stateChecks1 :
    compactCertificate541.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (14185823665431 / 160000000000)) (orderedInterval (84393282720 / 1000000000000) (84393282728 / 1000000000000), orderedInterval (7140543171 / 1000000000000) (7140543178 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (38105117766507 / 160000000000)) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (103462807237119 / 160000000000)) (orderedInterval (8056144993 / 1000000000000) (8056144994 / 1000000000000), orderedInterval (30318662745 / 1000000000000) (30318662746 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_stateChecks2 :
    compactCertificate541.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (76210235533047 / 160000000000)) (orderedInterval (-15006540963 / 1000000000000) (-15006540757 / 1000000000000), orderedInterval (33352805883 / 1000000000000) (33352806089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (130587537547731 / 160000000000)) (orderedInterval (3987510494 / 1000000000000) (3987510495 / 1000000000000), orderedInterval (27640036673 / 1000000000000) (27640036674 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (96190189111929 / 160000000000)) (orderedInterval (-30468127953 / 1000000000000) (-30468088197 / 1000000000000), orderedInterval (11454630236 / 1000000000000) (11454669993 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_stateChecks3 :
    compactCertificate541.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (147580486514967 / 160000000000)) (orderedInterval (-11779273873 / 1000000000000) (-11779273859 / 1000000000000), orderedInterval (23489203438 / 1000000000000) (23489203452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (85205633616543 / 160000000000)) (orderedInterval (-23577409701 / 1000000000000) (-23577402893 / 1000000000000), orderedInterval (25311597429 / 1000000000000) (25311604238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 301 12 (151198892068587 / 160000000000)) (orderedInterval (-4108307698 / 1000000000000) (-4108307697 / 1000000000000), orderedInterval (-25625907568 / 1000000000000) (-25625907567 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_stateChecks4 :
    compactCertificate541.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (141269617974903 / 160000000000)) (orderedInterval (-21570444902 / 1000000000000) (-21570444901 / 1000000000000), orderedInterval (-15979737562 / 1000000000000) (-15979737561 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (100816665288999 / 160000000000)) (orderedInterval (17173143737 / 1000000000000) (17173144246 / 1000000000000), orderedInterval (-26761034687 / 1000000000000) (-26761034179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (114315353299521 / 160000000000)) (orderedInterval (-25543506319 / 1000000000000) (-25543466434 / 1000000000000), orderedInterval (15463462559 / 1000000000000) (15463502445 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_stateChecks5 :
    compactCertificate541.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (95304223606449 / 160000000000)) (orderedInterval (-14689668788 / 1000000000000) (-14689668626 / 1000000000000), orderedInterval (29218374064 / 1000000000000) (29218374226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (84204171843429 / 160000000000)) (orderedInterval (-23098676131 / 1000000000000) (-23098670647 / 1000000000000), orderedInterval (26024253959 / 1000000000000) (26024259444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (24405651015471 / 32000000000)) (orderedInterval (-1582855443 / 1000000000000) (-1582855442 / 1000000000000), orderedInterval (-28847057630 / 1000000000000) (-28847057629 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_stateChecks6 :
    compactCertificate541.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (67507315107837 / 160000000000)) (orderedInterval (38337893234 / 1000000000000) (38337895464 / 1000000000000), orderedInterval (-6295711763 / 1000000000000) (-6295709532 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (57226698639957 / 160000000000)) (orderedInterval (12884324977 / 1000000000000) (12884324978 / 1000000000000), orderedInterval (40155604082 / 1000000000000) (40155604083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (35809810888071 / 160000000000)) (orderedInterval (-53312820131 / 1000000000000) (-53312820076 / 1000000000000), orderedInterval (-1358953076 / 1000000000000) (-1358953022 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_stateChecks7 :
    compactCertificate541.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (19258635393657 / 160000000000)) (orderedInterval (71282636604 / 1000000000000) (71282637184 / 1000000000000), orderedInterval (-14709850364 / 1000000000000) (-14709849783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (52290941431971 / 160000000000)) (orderedInterval (33953856956 / 1000000000000) (33953856957 / 1000000000000), orderedInterval (28144977975 / 1000000000000) (28144977976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (71398810035267 / 160000000000)) (orderedInterval (30085224953 / 1000000000000) (30085224954 / 1000000000000), orderedInterval (22802702362 / 1000000000000) (22802702363 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_stateChecks8 :
    compactCertificate541.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (30190189111929 / 160000000000)) (orderedInterval (48170303761 / 1000000000000) (48170303762 / 1000000000000), orderedInterval (32330535797 / 1000000000000) (32330535798 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (122721442630809 / 160000000000)) (orderedInterval (27300198657 / 1000000000000) (27300198697 / 1000000000000), orderedInterval (9185572176 / 1000000000000) (9185572215 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (81972236267031 / 160000000000)) (orderedInterval (-30257053802 / 1000000000000) (-30257053801 / 1000000000000), orderedInterval (-18056821077 / 1000000000000) (-18056821076 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_states : ∀ j,
    BesselStateValid (compactCertificate541.point j) (compactCertificate541.state j) :=
  compactCertificate541.statesValid_of_checks3 compactCertificate541_stateChecks0
    compactCertificate541_stateChecks1 compactCertificate541_stateChecks2
    compactCertificate541_stateChecks3 compactCertificate541_stateChecks4
    compactCertificate541_stateChecks5 compactCertificate541_stateChecks6
    compactCertificate541_stateChecks7 compactCertificate541_stateChecks8

theorem compactCertificate541_chunkChecks0_0 :
    compactCertificate541.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (825 / 2) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38747275493 / 1000000000000) (-38747273281 / 1000000000000), orderedInterval (6525260734 / 1000000000000) (6525262947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (48615301280733 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4745831067 / 1000000000000) (4745831074 / 1000000000000), orderedInterval (-45534590379 / 1000000000000) (-45534590372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (15721189569789 / 32000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32969858101 / 1000000000000) (32969897324 / 1000000000000), orderedInterval (-14483719960 / 1000000000000) (-14483680738 / 1000000000000)))) (orderedInterval (-13379132796 / 1000000000000) (-13379129589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (14185823665431 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (84393282720 / 1000000000000) (84393282728 / 1000000000000), orderedInterval (7140543171 / 1000000000000) (7140543178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (103462807237119 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8056144993 / 1000000000000) (8056144994 / 1000000000000), orderedInterval (30318662745 / 1000000000000) (30318662746 / 1000000000000)))) (orderedInterval (-1148837270 / 1000000000000) (-1148837220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (76210235533047 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15006540963 / 1000000000000) (-15006540757 / 1000000000000), orderedInterval (33352805883 / 1000000000000) (33352806089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (130587537547731 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3987510494 / 1000000000000) (3987510495 / 1000000000000), orderedInterval (27640036673 / 1000000000000) (27640036674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (96190189111929 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30468127953 / 1000000000000) (-30468088197 / 1000000000000), orderedInterval (11454630236 / 1000000000000) (11454669993 / 1000000000000)))) (orderedInterval (-859345329 / 1000000000000) (-859344344 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks0_1 :
    compactCertificate541.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (147580486514967 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11779273873 / 1000000000000) (-11779273859 / 1000000000000), orderedInterval (23489203438 / 1000000000000) (23489203452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (85205633616543 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23577409701 / 1000000000000) (-23577402893 / 1000000000000), orderedInterval (25311597429 / 1000000000000) (25311604238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (151198892068587 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4108307698 / 1000000000000) (-4108307697 / 1000000000000), orderedInterval (-25625907568 / 1000000000000) (-25625907567 / 1000000000000)))) (orderedInterval (-237877526 / 1000000000000) (-237876855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (141269617974903 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21570444902 / 1000000000000) (-21570444901 / 1000000000000), orderedInterval (-15979737562 / 1000000000000) (-15979737561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (100816665288999 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173143737 / 1000000000000) (17173144246 / 1000000000000), orderedInterval (-26761034687 / 1000000000000) (-26761034179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (114315353299521 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25543506319 / 1000000000000) (-25543466434 / 1000000000000), orderedInterval (15463462559 / 1000000000000) (15463502445 / 1000000000000)))) (orderedInterval (2142619415 / 1000000000000) (2142619715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (95304223606449 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14689668788 / 1000000000000) (-14689668626 / 1000000000000), orderedInterval (29218374064 / 1000000000000) (29218374226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (84204171843429 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23098676131 / 1000000000000) (-23098670647 / 1000000000000), orderedInterval (26024253959 / 1000000000000) (26024259444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (24405651015471 / 32000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1582855443 / 1000000000000) (-1582855442 / 1000000000000), orderedInterval (-28847057630 / 1000000000000) (-28847057629 / 1000000000000)))) (orderedInterval (1111701345 / 1000000000000) (1111701701 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks0_2 :
    compactCertificate541.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (67507315107837 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38337893234 / 1000000000000) (38337895464 / 1000000000000), orderedInterval (-6295711763 / 1000000000000) (-6295709532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (57226698639957 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12884324977 / 1000000000000) (12884324978 / 1000000000000), orderedInterval (40155604082 / 1000000000000) (40155604083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (35809810888071 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53312820131 / 1000000000000) (-53312820076 / 1000000000000), orderedInterval (-1358953076 / 1000000000000) (-1358953022 / 1000000000000)))) (orderedInterval (-8594805313 / 1000000000000) (-8594804851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (19258635393657 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71282636604 / 1000000000000) (71282637184 / 1000000000000), orderedInterval (-14709850364 / 1000000000000) (-14709849783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (52290941431971 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33953856956 / 1000000000000) (33953856957 / 1000000000000), orderedInterval (28144977975 / 1000000000000) (28144977976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (71398810035267 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30085224953 / 1000000000000) (30085224954 / 1000000000000), orderedInterval (22802702362 / 1000000000000) (22802702363 / 1000000000000)))) (orderedInterval (-4392246372 / 1000000000000) (-4392246311 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (30190189111929 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48170303761 / 1000000000000) (48170303762 / 1000000000000), orderedInterval (32330535797 / 1000000000000) (32330535798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (122721442630809 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27300198657 / 1000000000000) (27300198697 / 1000000000000), orderedInterval (9185572176 / 1000000000000) (9185572215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (81972236267031 / 160000000000) 0 (IntervalRat.scale (825 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30257053802 / 1000000000000) (-30257053801 / 1000000000000), orderedInterval (-18056821077 / 1000000000000) (-18056821076 / 1000000000000)))) (orderedInterval (3745127569 / 1000000000000) (3745127687 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks0 :
    compactCertificate541.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate541.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate541_chunkChecks0_0
    compactCertificate541_chunkChecks0_1 compactCertificate541_chunkChecks0_2

theorem compactCertificate541_chunkChecks1_0 :
    compactCertificate541.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (825 / 2) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38747275493 / 1000000000000) (-38747273281 / 1000000000000), orderedInterval (6525260734 / 1000000000000) (6525262947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (48615301280733 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4745831067 / 1000000000000) (4745831074 / 1000000000000), orderedInterval (-45534590379 / 1000000000000) (-45534590372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (15721189569789 / 32000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32969858101 / 1000000000000) (32969897324 / 1000000000000), orderedInterval (-14483719960 / 1000000000000) (-14483680738 / 1000000000000)))) (orderedInterval (1261596359 / 1000000000000) (1261600010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (14185823665431 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (84393282720 / 1000000000000) (84393282728 / 1000000000000), orderedInterval (7140543171 / 1000000000000) (7140543178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (103462807237119 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8056144993 / 1000000000000) (8056144994 / 1000000000000), orderedInterval (30318662745 / 1000000000000) (30318662746 / 1000000000000)))) (orderedInterval (-2323700490 / 1000000000000) (-2323700433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (76210235533047 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15006540963 / 1000000000000) (-15006540757 / 1000000000000), orderedInterval (33352805883 / 1000000000000) (33352806089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (130587537547731 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3987510494 / 1000000000000) (3987510495 / 1000000000000), orderedInterval (27640036673 / 1000000000000) (27640036674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (96190189111929 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30468127953 / 1000000000000) (-30468088197 / 1000000000000), orderedInterval (11454630236 / 1000000000000) (11454669993 / 1000000000000)))) (orderedInterval (-1283345706 / 1000000000000) (-1283344265 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks1_1 :
    compactCertificate541.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (147580486514967 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11779273873 / 1000000000000) (-11779273859 / 1000000000000), orderedInterval (23489203438 / 1000000000000) (23489203452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (85205633616543 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23577409701 / 1000000000000) (-23577402893 / 1000000000000), orderedInterval (25311597429 / 1000000000000) (25311604238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (151198892068587 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4108307698 / 1000000000000) (-4108307697 / 1000000000000), orderedInterval (-25625907568 / 1000000000000) (-25625907567 / 1000000000000)))) (orderedInterval (-15257108943 / 1000000000000) (-15257107947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (141269617974903 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21570444902 / 1000000000000) (-21570444901 / 1000000000000), orderedInterval (-15979737562 / 1000000000000) (-15979737561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (100816665288999 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173143737 / 1000000000000) (17173144246 / 1000000000000), orderedInterval (-26761034687 / 1000000000000) (-26761034179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (114315353299521 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25543506319 / 1000000000000) (-25543466434 / 1000000000000), orderedInterval (15463462559 / 1000000000000) (15463502445 / 1000000000000)))) (orderedInterval (-3383611589 / 1000000000000) (-3383611086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (95304223606449 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14689668788 / 1000000000000) (-14689668626 / 1000000000000), orderedInterval (29218374064 / 1000000000000) (29218374226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (84204171843429 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23098676131 / 1000000000000) (-23098670647 / 1000000000000), orderedInterval (26024253959 / 1000000000000) (26024259444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (24405651015471 / 32000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1582855443 / 1000000000000) (-1582855442 / 1000000000000), orderedInterval (-28847057630 / 1000000000000) (-28847057629 / 1000000000000)))) (orderedInterval (-2778448655 / 1000000000000) (-2778448194 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks1_2 :
    compactCertificate541.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (67507315107837 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38337893234 / 1000000000000) (38337895464 / 1000000000000), orderedInterval (-6295711763 / 1000000000000) (-6295709532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (57226698639957 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12884324977 / 1000000000000) (12884324978 / 1000000000000), orderedInterval (40155604082 / 1000000000000) (40155604083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (35809810888071 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53312820131 / 1000000000000) (-53312820076 / 1000000000000), orderedInterval (-1358953076 / 1000000000000) (-1358953022 / 1000000000000)))) (orderedInterval (-965062128 / 1000000000000) (-965061666 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (19258635393657 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71282636604 / 1000000000000) (71282637184 / 1000000000000), orderedInterval (-14709850364 / 1000000000000) (-14709849783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (52290941431971 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33953856956 / 1000000000000) (33953856957 / 1000000000000), orderedInterval (28144977975 / 1000000000000) (28144977976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (71398810035267 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30085224953 / 1000000000000) (30085224954 / 1000000000000), orderedInterval (22802702362 / 1000000000000) (22802702363 / 1000000000000)))) (orderedInterval (-2317159420 / 1000000000000) (-2317159372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (30190189111929 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48170303761 / 1000000000000) (48170303762 / 1000000000000), orderedInterval (32330535797 / 1000000000000) (32330535798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (122721442630809 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27300198657 / 1000000000000) (27300198697 / 1000000000000), orderedInterval (9185572176 / 1000000000000) (9185572215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (81972236267031 / 160000000000) 1 (IntervalRat.scale (825 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30257053802 / 1000000000000) (-30257053801 / 1000000000000), orderedInterval (-18056821077 / 1000000000000) (-18056821076 / 1000000000000)))) (orderedInterval (2906658028 / 1000000000000) (2906658194 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks1 :
    compactCertificate541.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate541.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate541_chunkChecks1_0
    compactCertificate541_chunkChecks1_1 compactCertificate541_chunkChecks1_2

theorem compactCertificate541_chunkChecks2_0 :
    compactCertificate541.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (825 / 2) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38747275493 / 1000000000000) (-38747273281 / 1000000000000), orderedInterval (6525260734 / 1000000000000) (6525262947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (48615301280733 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4745831067 / 1000000000000) (4745831074 / 1000000000000), orderedInterval (-45534590379 / 1000000000000) (-45534590372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (15721189569789 / 32000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32969858101 / 1000000000000) (32969897324 / 1000000000000), orderedInterval (-14483719960 / 1000000000000) (-14483680738 / 1000000000000)))) (orderedInterval (12586663254 / 1000000000000) (12586667442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (14185823665431 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (84393282720 / 1000000000000) (84393282728 / 1000000000000), orderedInterval (7140543171 / 1000000000000) (7140543178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (103462807237119 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8056144993 / 1000000000000) (8056144994 / 1000000000000), orderedInterval (30318662745 / 1000000000000) (30318662746 / 1000000000000)))) (orderedInterval (1342161997 / 1000000000000) (1342162075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (76210235533047 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15006540963 / 1000000000000) (-15006540757 / 1000000000000), orderedInterval (33352805883 / 1000000000000) (33352806089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (130587537547731 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3987510494 / 1000000000000) (3987510495 / 1000000000000), orderedInterval (27640036673 / 1000000000000) (27640036674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (96190189111929 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30468127953 / 1000000000000) (-30468088197 / 1000000000000), orderedInterval (11454630236 / 1000000000000) (11454669993 / 1000000000000)))) (orderedInterval (2048686117 / 1000000000000) (2048688234 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks2_1 :
    compactCertificate541.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (147580486514967 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11779273873 / 1000000000000) (-11779273859 / 1000000000000), orderedInterval (23489203438 / 1000000000000) (23489203452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (85205633616543 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23577409701 / 1000000000000) (-23577402893 / 1000000000000), orderedInterval (25311597429 / 1000000000000) (25311604238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (151198892068587 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4108307698 / 1000000000000) (-4108307697 / 1000000000000), orderedInterval (-25625907568 / 1000000000000) (-25625907567 / 1000000000000)))) (orderedInterval (-4451654008 / 1000000000000) (-4451652426 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (141269617974903 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21570444902 / 1000000000000) (-21570444901 / 1000000000000), orderedInterval (-15979737562 / 1000000000000) (-15979737561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (100816665288999 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173143737 / 1000000000000) (17173144246 / 1000000000000), orderedInterval (-26761034687 / 1000000000000) (-26761034179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (114315353299521 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25543506319 / 1000000000000) (-25543466434 / 1000000000000), orderedInterval (15463462559 / 1000000000000) (15463502445 / 1000000000000)))) (orderedInterval (-5952893562 / 1000000000000) (-5952892710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (95304223606449 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14689668788 / 1000000000000) (-14689668626 / 1000000000000), orderedInterval (29218374064 / 1000000000000) (29218374226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (84204171843429 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23098676131 / 1000000000000) (-23098670647 / 1000000000000), orderedInterval (26024253959 / 1000000000000) (26024259444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (24405651015471 / 32000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1582855443 / 1000000000000) (-1582855442 / 1000000000000), orderedInterval (-28847057630 / 1000000000000) (-28847057629 / 1000000000000)))) (orderedInterval (-1652633200 / 1000000000000) (-1652632599 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks2_2 :
    compactCertificate541.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (67507315107837 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38337893234 / 1000000000000) (38337895464 / 1000000000000), orderedInterval (-6295711763 / 1000000000000) (-6295709532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (57226698639957 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12884324977 / 1000000000000) (12884324978 / 1000000000000), orderedInterval (40155604082 / 1000000000000) (40155604083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (35809810888071 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53312820131 / 1000000000000) (-53312820076 / 1000000000000), orderedInterval (-1358953076 / 1000000000000) (-1358953022 / 1000000000000)))) (orderedInterval (7474668571 / 1000000000000) (7474669037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (19258635393657 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71282636604 / 1000000000000) (71282637184 / 1000000000000), orderedInterval (-14709850364 / 1000000000000) (-14709849783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (52290941431971 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33953856956 / 1000000000000) (33953856957 / 1000000000000), orderedInterval (28144977975 / 1000000000000) (28144977976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (71398810035267 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30085224953 / 1000000000000) (30085224954 / 1000000000000), orderedInterval (22802702362 / 1000000000000) (22802702363 / 1000000000000)))) (orderedInterval (3299564080 / 1000000000000) (3299564126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (30190189111929 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48170303761 / 1000000000000) (48170303762 / 1000000000000), orderedInterval (32330535797 / 1000000000000) (32330535798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (122721442630809 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27300198657 / 1000000000000) (27300198697 / 1000000000000), orderedInterval (9185572176 / 1000000000000) (9185572215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (81972236267031 / 160000000000) 2 (IntervalRat.scale (825 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30257053802 / 1000000000000) (-30257053801 / 1000000000000), orderedInterval (-18056821077 / 1000000000000) (-18056821076 / 1000000000000)))) (orderedInterval (-1141645874 / 1000000000000) (-1141645626 / 1000000000000))) = true
  rfl'

theorem compactCertificate541_chunkChecks2 :
    compactCertificate541.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate541.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate541_chunkChecks2_0
    compactCertificate541_chunkChecks2_1 compactCertificate541_chunkChecks2_2

theorem compactCertificate541_chunkChecks3_0 :
    compactCertificate541.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (825 / 2) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38747275493 / 1000000000000) (-38747273281 / 1000000000000), orderedInterval (6525260734 / 1000000000000) (6525262947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (48615301280733 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4745831067 / 1000000000000) (4745831074 / 1000000000000), orderedInterval (-45534590379 / 1000000000000) (-45534590372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (15721189569789 / 32000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32969858101 / 1000000000000) (32969897324 / 1000000000000), orderedInterval (-14483719960 / 1000000000000) (-14483680738 / 1000000000000)))) (orderedInterval (-1011460203 / 1000000000000) (-1011455384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (14185823665431 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (84393282720 / 1000000000000) (84393282728 / 1000000000000), orderedInterval (7140543171 / 1000000000000) (7140543178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (103462807237119 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8056144993 / 1000000000000) (8056144994 / 1000000000000), orderedInterval (30318662745 / 1000000000000) (30318662746 / 1000000000000)))) (orderedInterval (7943310452 / 1000000000000) (7943310569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (76210235533047 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15006540963 / 1000000000000) (-15006540757 / 1000000000000), orderedInterval (33352805883 / 1000000000000) (33352806089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (130587537547731 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3987510494 / 1000000000000) (3987510495 / 1000000000000), orderedInterval (27640036673 / 1000000000000) (27640036674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (96190189111929 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30468127953 / 1000000000000) (-30468088197 / 1000000000000), orderedInterval (11454630236 / 1000000000000) (11454669993 / 1000000000000)))) (orderedInterval (5741648734 / 1000000000000) (5741651844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate541_chunkChecks3_1 :
    compactCertificate541.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (147580486514967 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11779273873 / 1000000000000) (-11779273859 / 1000000000000), orderedInterval (23489203438 / 1000000000000) (23489203452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (85205633616543 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23577409701 / 1000000000000) (-23577402893 / 1000000000000), orderedInterval (25311597429 / 1000000000000) (25311604238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (151198892068587 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4108307698 / 1000000000000) (-4108307697 / 1000000000000), orderedInterval (-25625907568 / 1000000000000) (-25625907567 / 1000000000000)))) (orderedInterval (86437831561 / 1000000000000) (86437834270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (141269617974903 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21570444902 / 1000000000000) (-21570444901 / 1000000000000), orderedInterval (-15979737562 / 1000000000000) (-15979737561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (100816665288999 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173143737 / 1000000000000) (17173144246 / 1000000000000), orderedInterval (-26761034687 / 1000000000000) (-26761034179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (114315353299521 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25543506319 / 1000000000000) (-25543466434 / 1000000000000), orderedInterval (15463462559 / 1000000000000) (15463502445 / 1000000000000)))) (orderedInterval (6611643310 / 1000000000000) (6611644756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (95304223606449 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14689668788 / 1000000000000) (-14689668626 / 1000000000000), orderedInterval (29218374064 / 1000000000000) (29218374226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (84204171843429 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23098676131 / 1000000000000) (-23098670647 / 1000000000000), orderedInterval (26024253959 / 1000000000000) (26024259444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (24405651015471 / 32000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1582855443 / 1000000000000) (-1582855442 / 1000000000000), orderedInterval (-28847057630 / 1000000000000) (-28847057629 / 1000000000000)))) (orderedInterval (6749128368 / 1000000000000) (6749129158 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate541_chunkChecks3_2 :
    compactCertificate541.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (67507315107837 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38337893234 / 1000000000000) (38337895464 / 1000000000000), orderedInterval (-6295711763 / 1000000000000) (-6295709532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (57226698639957 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12884324977 / 1000000000000) (12884324978 / 1000000000000), orderedInterval (40155604082 / 1000000000000) (40155604083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (35809810888071 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53312820131 / 1000000000000) (-53312820076 / 1000000000000), orderedInterval (-1358953076 / 1000000000000) (-1358953022 / 1000000000000)))) (orderedInterval (393332278 / 1000000000000) (393332750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (19258635393657 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71282636604 / 1000000000000) (71282637184 / 1000000000000), orderedInterval (-14709850364 / 1000000000000) (-14709849783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (52290941431971 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33953856956 / 1000000000000) (33953856957 / 1000000000000), orderedInterval (28144977975 / 1000000000000) (28144977976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (71398810035267 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30085224953 / 1000000000000) (30085224954 / 1000000000000), orderedInterval (22802702362 / 1000000000000) (22802702363 / 1000000000000)))) (orderedInterval (2515262442 / 1000000000000) (2515262488 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (30190189111929 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48170303761 / 1000000000000) (48170303762 / 1000000000000), orderedInterval (32330535797 / 1000000000000) (32330535798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (122721442630809 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27300198657 / 1000000000000) (27300198697 / 1000000000000), orderedInterval (9185572176 / 1000000000000) (9185572215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (81972236267031 / 160000000000) 3 (IntervalRat.scale (825 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30257053802 / 1000000000000) (-30257053801 / 1000000000000), orderedInterval (-18056821077 / 1000000000000) (-18056821076 / 1000000000000)))) (orderedInterval (-1699806567 / 1000000000000) (-1699806181 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate541_chunkChecks3 :
    compactCertificate541.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate541.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate541_chunkChecks3_0
    compactCertificate541_chunkChecks3_1 compactCertificate541_chunkChecks3_2

theorem compactCertificate541_chunkChecks4_0 :
    compactCertificate541.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (825 / 2) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38747275493 / 1000000000000) (-38747273281 / 1000000000000), orderedInterval (6525260734 / 1000000000000) (6525262947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (48615301280733 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4745831067 / 1000000000000) (4745831074 / 1000000000000), orderedInterval (-45534590379 / 1000000000000) (-45534590372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (15721189569789 / 32000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32969858101 / 1000000000000) (32969897324 / 1000000000000), orderedInterval (-14483719960 / 1000000000000) (-14483680738 / 1000000000000)))) (orderedInterval (-11447272515 / 1000000000000) (-11447266933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (14185823665431 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (84393282720 / 1000000000000) (84393282728 / 1000000000000), orderedInterval (7140543171 / 1000000000000) (7140543178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (38105117766507 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9297788530 / 1000000000000) (9297788531 / 1000000000000), orderedInterval (50839760502 / 1000000000000) (50839760503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (103462807237119 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8056144993 / 1000000000000) (8056144994 / 1000000000000), orderedInterval (30318662745 / 1000000000000) (30318662746 / 1000000000000)))) (orderedInterval (-3461296055 / 1000000000000) (-3461295875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (76210235533047 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15006540963 / 1000000000000) (-15006540757 / 1000000000000), orderedInterval (33352805883 / 1000000000000) (33352806089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (130587537547731 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3987510494 / 1000000000000) (3987510495 / 1000000000000), orderedInterval (27640036673 / 1000000000000) (27640036674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (96190189111929 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30468127953 / 1000000000000) (-30468088197 / 1000000000000), orderedInterval (11454630236 / 1000000000000) (11454669993 / 1000000000000)))) (orderedInterval (-5235058837 / 1000000000000) (-5235054246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate541_chunkChecks4_1 :
    compactCertificate541.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (147580486514967 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11779273873 / 1000000000000) (-11779273859 / 1000000000000), orderedInterval (23489203438 / 1000000000000) (23489203452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (85205633616543 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-23577409701 / 1000000000000) (-23577402893 / 1000000000000), orderedInterval (25311597429 / 1000000000000) (25311604238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (151198892068587 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4108307698 / 1000000000000) (-4108307697 / 1000000000000), orderedInterval (-25625907568 / 1000000000000) (-25625907567 / 1000000000000)))) (orderedInterval (30968327575 / 1000000000000) (30968332581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (141269617974903 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21570444902 / 1000000000000) (-21570444901 / 1000000000000), orderedInterval (-15979737562 / 1000000000000) (-15979737561 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (100816665288999 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173143737 / 1000000000000) (17173144246 / 1000000000000), orderedInterval (-26761034687 / 1000000000000) (-26761034179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (114315353299521 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25543506319 / 1000000000000) (-25543466434 / 1000000000000), orderedInterval (15463462559 / 1000000000000) (15463502445 / 1000000000000)))) (orderedInterval (18146661410 / 1000000000000) (18146663883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (95304223606449 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14689668788 / 1000000000000) (-14689668626 / 1000000000000), orderedInterval (29218374064 / 1000000000000) (29218374226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (84204171843429 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23098676131 / 1000000000000) (-23098670647 / 1000000000000), orderedInterval (26024253959 / 1000000000000) (26024259444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (24405651015471 / 32000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1582855443 / 1000000000000) (-1582855442 / 1000000000000), orderedInterval (-28847057630 / 1000000000000) (-28847057629 / 1000000000000)))) (orderedInterval (2258361693 / 1000000000000) (2258362744 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate541_chunkChecks4_2 :
    compactCertificate541.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (67507315107837 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38337893234 / 1000000000000) (38337895464 / 1000000000000), orderedInterval (-6295711763 / 1000000000000) (-6295709532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (57226698639957 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12884324977 / 1000000000000) (12884324978 / 1000000000000), orderedInterval (40155604082 / 1000000000000) (40155604083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (35809810888071 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53312820131 / 1000000000000) (-53312820076 / 1000000000000), orderedInterval (-1358953076 / 1000000000000) (-1358953022 / 1000000000000)))) (orderedInterval (-7273867390 / 1000000000000) (-7273866910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (19258635393657 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71282636604 / 1000000000000) (71282637184 / 1000000000000), orderedInterval (-14709850364 / 1000000000000) (-14709849783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (52290941431971 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33953856956 / 1000000000000) (33953856957 / 1000000000000), orderedInterval (28144977975 / 1000000000000) (28144977976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (71398810035267 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30085224953 / 1000000000000) (30085224954 / 1000000000000), orderedInterval (22802702362 / 1000000000000) (22802702363 / 1000000000000)))) (orderedInterval (-3483085548 / 1000000000000) (-3483085500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (30190189111929 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48170303761 / 1000000000000) (48170303762 / 1000000000000), orderedInterval (32330535797 / 1000000000000) (32330535798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (122721442630809 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27300198657 / 1000000000000) (27300198697 / 1000000000000), orderedInterval (9185572176 / 1000000000000) (9185572215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (81972236267031 / 160000000000) 4 (IntervalRat.scale (825 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30257053802 / 1000000000000) (-30257053801 / 1000000000000), orderedInterval (-18056821077 / 1000000000000) (-18056821076 / 1000000000000)))) (orderedInterval (-13035143786 / 1000000000000) (-13035143160 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate541_chunkChecks4 :
    compactCertificate541.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate541.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate541_chunkChecks4_0
    compactCertificate541_chunkChecks4_1 compactCertificate541_chunkChecks4_2

theorem compactCertificate541_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate541.chunkCheck r b = true :=
  compactCertificate541.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate541_chunkChecks0
    · exact compactCertificate541_chunkChecks1
    · exact compactCertificate541_chunkChecks2
    · exact compactCertificate541_chunkChecks3
    · exact compactCertificate541_chunkChecks4)

theorem compactCertificate541_coefficient0 :
    compactCertificate541.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate541_coefficient1 :
    compactCertificate541.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate541_coefficient2 :
    compactCertificate541.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate541_coefficient3 :
    compactCertificate541.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate541_coefficient4 :
    compactCertificate541.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate541_coefficients : ∀ r : Fin 5,
    compactCertificate541.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate541_coefficient0
  · exact compactCertificate541_coefficient1
  · exact compactCertificate541_coefficient2
  · exact compactCertificate541_coefficient3
  · exact compactCertificate541_coefficient4

theorem compactCertificate541_lower : (1 : ℚ) ≤ compactCertificate541.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate541, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate541_proves {t : ℝ} (ht : t ∈ compactCertificate541.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate541.proves compactCertificate541_states compactCertificate541_chunks
    compactCertificate541_coefficients compactCertificate541_lower ht

end Erdos232
