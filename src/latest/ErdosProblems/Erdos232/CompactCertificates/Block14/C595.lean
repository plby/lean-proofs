/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate595 : CompactCertificate where
  left := 466
  right := 467
  center := 933 / 2
  grid := fun i =>
    match i.val with
    | 0 => 149
    | 1 => 109
    | 2 => 177
    | 3 => 32
    | 4 => 86
    | 5 => 233
    | 6 => 172
    | 7 => 294
    | 8 => 217
    | 9 => 332
    | 10 => 192
    | 11 => 340
    | 12 => 318
    | 13 => 227
    | 14 => 257
    | 15 => 215
    | 16 => 190
    | 17 => 275
    | 18 => 152
    | 19 => 129
    | 20 => 81
    | 21 => 43
    | 22 => 118
    | 23 => 161
    | 24 => 68
    | 25 => 276
    | _ => 185
  point := fun i =>
    match i.val with
    | 0 => 933 / 2
    | 1 => 1374487154391633 / 4000000000000
    | 2 => 444480905109489 / 800000000000
    | 3 => 401071923631731 / 4000000000000
    | 4 => 1077335602307607 / 4000000000000
    | 5 => 2925175731885819 / 4000000000000
    | 6 => 2154671204616147 / 4000000000000
    | 7 => 3692065834304031 / 4000000000000
    | 8 => 2719558983073629 / 4000000000000
    | 9 => 4172502846014067 / 4000000000000
    | 10 => 2408995641340443 / 4000000000000
    | 11 => 4274805039393687 / 4000000000000
    | 12 => 3994077380926803 / 4000000000000
    | 13 => 2850362082261699 / 4000000000000
    | 14 => 3232006806922821 / 4000000000000
    | 15 => 2694510321964149 / 4000000000000
    | 16 => 2380681585755129 / 4000000000000
    | 17 => 690014315073771 / 800000000000
    | 18 => 1908615908957937 / 4000000000000
    | 19 => 1617954843366057 / 4000000000000
    | 20 => 1012441016926371 / 4000000000000
    | 21 => 544494146129757 / 4000000000000
    | 22 => 1478407525940271 / 4000000000000
    | 23 => 2018639083724367 / 4000000000000
    | 24 => 853558983073629 / 4000000000000
    | 25 => 3469669878016509 / 4000000000000
    | _ => 2317578679913331 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (26811560853 / 1000000000000) (26811578342 / 1000000000000), orderedInterval (-25441582583 / 1000000000000) (-25441565093 / 1000000000000))
    | 1 => (orderedInterval (-39604154400 / 1000000000000) (-39604136609 / 1000000000000), orderedInterval (16915437727 / 1000000000000) (16915455518 / 1000000000000))
    | 2 => (orderedInterval (-10789503898 / 1000000000000) (-10789503897 / 1000000000000), orderedInterval (-32074687806 / 1000000000000) (-32074687805 / 1000000000000))
    | 3 => (orderedInterval (39672747224 / 1000000000000) (39672747225 / 1000000000000), orderedInterval (68905688247 / 1000000000000) (68905688248 / 1000000000000))
    | 4 => (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))
    | 5 => (orderedInterval (-2595194381 / 1000000000000) (-2595194380 / 1000000000000), orderedInterval (-29388768429 / 1000000000000) (-29388768428 / 1000000000000))
    | 6 => (orderedInterval (-26949852994 / 1000000000000) (-26949824456 / 1000000000000), orderedInterval (21368552493 / 1000000000000) (21368581030 / 1000000000000))
    | 7 => (orderedInterval (4533222451 / 1000000000000) (4533222452 / 1000000000000), orderedInterval (25865798790 / 1000000000000) (25865798791 / 1000000000000))
    | 8 => (orderedInterval (26552906695 / 1000000000000) (26552964125 / 1000000000000), orderedInterval (-15228067114 / 1000000000000) (-15228009684 / 1000000000000))
    | 9 => (orderedInterval (19385684421 / 1000000000000) (19385684423 / 1000000000000), orderedInterval (15303949467 / 1000000000000) (15303949469 / 1000000000000))
    | 10 => (orderedInterval (-4912900934 / 1000000000000) (-4912900933 / 1000000000000), orderedInterval (32143378879 / 1000000000000) (32143378881 / 1000000000000))
    | 11 => (orderedInterval (23787529259 / 1000000000000) (23787530386 / 1000000000000), orderedInterval (5452216813 / 1000000000000) (5452217940 / 1000000000000))
    | 12 => (orderedInterval (6933187515 / 1000000000000) (6933187516 / 1000000000000), orderedInterval (24276041502 / 1000000000000) (24276041503 / 1000000000000))
    | 13 => (orderedInterval (-6936643472 / 1000000000000) (-6936643471 / 1000000000000), orderedInterval (-29068679313 / 1000000000000) (-29068679312 / 1000000000000))
    | 14 => (orderedInterval (-27649661702 / 1000000000000) (-27649661276 / 1000000000000), orderedInterval (-4819229413 / 1000000000000) (-4819228988 / 1000000000000))
    | 15 => (orderedInterval (26349037753 / 1000000000000) (26349086863 / 1000000000000), orderedInterval (-15855890565 / 1000000000000) (-15855841455 / 1000000000000))
    | 16 => (orderedInterval (-26546269399 / 1000000000000) (-26546235935 / 1000000000000), orderedInterval (19125666204 / 1000000000000) (19125699667 / 1000000000000))
    | 17 => (orderedInterval (16111723091 / 1000000000000) (16111723346 / 1000000000000), orderedInterval (-21884142453 / 1000000000000) (-21884142198 / 1000000000000))
    | 18 => (orderedInterval (14795033169 / 1000000000000) (14795033170 / 1000000000000), orderedInterval (33380745599 / 1000000000000) (33380745600 / 1000000000000))
    | 19 => (orderedInterval (-331166531 / 1000000000000) (-331166529 / 1000000000000), orderedInterval (-39670476005 / 1000000000000) (-39670476004 / 1000000000000))
    | 20 => (orderedInterval (27225611239 / 1000000000000) (27225615964 / 1000000000000), orderedInterval (-42172136168 / 1000000000000) (-42172131442 / 1000000000000))
    | 21 => (orderedInterval (-66282107917 / 1000000000000) (-66282106760 / 1000000000000), orderedInterval (17078959576 / 1000000000000) (17078960733 / 1000000000000))
    | 22 => (orderedInterval (-13094315317 / 1000000000000) (-13094315210 / 1000000000000), orderedInterval (39400292577 / 1000000000000) (39400292683 / 1000000000000))
    | 23 => (orderedInterval (12228716101 / 1000000000000) (12228716163 / 1000000000000), orderedInterval (-33357911272 / 1000000000000) (-33357911210 / 1000000000000))
    | 24 => (orderedInterval (28374782816 / 1000000000000) (28374782817 / 1000000000000), orderedInterval (46605152091 / 1000000000000) (46605152092 / 1000000000000))
    | 25 => (orderedInterval (24421744442 / 1000000000000) (24421744455 / 1000000000000), orderedInterval (11712123730 / 1000000000000) (11712123743 / 1000000000000))
    | _ => (orderedInterval (28154550147 / 1000000000000) (28154615606 / 1000000000000), orderedInterval (-17519650390 / 1000000000000) (-17519584931 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9624989838 / 1000000000000) (9624996968 / 1000000000000)
      | 1 => orderedInterval (-349065502 / 1000000000000) (-349065445 / 1000000000000)
      | 2 => orderedInterval (501908635 / 1000000000000) (501910049 / 1000000000000)
      | 3 => orderedInterval (-427070242 / 1000000000000) (-427069897 / 1000000000000)
      | 4 => orderedInterval (-641191133 / 1000000000000) (-641191075 / 1000000000000)
      | 5 => orderedInterval (2235946592 / 1000000000000) (2235949126 / 1000000000000)
      | 6 => orderedInterval (-1460532879 / 1000000000000) (-1460532607 / 1000000000000)
      | 7 => orderedInterval (583780762 / 1000000000000) (583780847 / 1000000000000)
      | _ => orderedInterval (-7099473708 / 1000000000000) (-7099461296 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12209725226 / 1000000000000) (-12209718135 / 1000000000000)
      | 1 => orderedInterval (4137688981 / 1000000000000) (4137689045 / 1000000000000)
      | 2 => orderedInterval (-2114915999 / 1000000000000) (-2114913930 / 1000000000000)
      | 3 => orderedInterval (-1230429882 / 1000000000000) (-1230429131 / 1000000000000)
      | 4 => orderedInterval (-5094714589 / 1000000000000) (-5094714495 / 1000000000000)
      | 5 => orderedInterval (-2696764984 / 1000000000000) (-2696761644 / 1000000000000)
      | 6 => orderedInterval (-4257259671 / 1000000000000) (-4257259478 / 1000000000000)
      | 7 => orderedInterval (1965412211 / 1000000000000) (1965412275 / 1000000000000)
      | _ => orderedInterval (2438408705 / 1000000000000) (2438424143 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9502673940 / 1000000000000) (-9502666861 / 1000000000000)
      | 1 => orderedInterval (-407980860 / 1000000000000) (-407980772 / 1000000000000)
      | 2 => orderedInterval (-811181454 / 1000000000000) (-811178420 / 1000000000000)
      | 3 => orderedInterval (85379814 / 1000000000000) (85381479 / 1000000000000)
      | 4 => orderedInterval (1695146864 / 1000000000000) (1695147021 / 1000000000000)
      | 5 => orderedInterval (-4511628155 / 1000000000000) (-4511623730 / 1000000000000)
      | 6 => orderedInterval (2209009345 / 1000000000000) (2209009494 / 1000000000000)
      | 7 => orderedInterval (801892037 / 1000000000000) (801892096 / 1000000000000)
      | _ => orderedInterval (14980958682 / 1000000000000) (14980977932 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (13221233936 / 1000000000000) (13221240999 / 1000000000000)
      | 1 => orderedInterval (-8381148688 / 1000000000000) (-8381148556 / 1000000000000)
      | 2 => orderedInterval (7320783866 / 1000000000000) (7320788316 / 1000000000000)
      | 3 => orderedInterval (15959879540 / 1000000000000) (15959883272 / 1000000000000)
      | 4 => orderedInterval (13964801044 / 1000000000000) (13964801309 / 1000000000000)
      | 5 => orderedInterval (6375367967 / 1000000000000) (6375373850 / 1000000000000)
      | 6 => orderedInterval (4462278259 / 1000000000000) (4462278384 / 1000000000000)
      | 7 => orderedInterval (-2785923943 / 1000000000000) (-2785923883 / 1000000000000)
      | _ => orderedInterval (-227649964 / 1000000000000) (-227625973 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9187868665 / 1000000000000) (9187875733 / 1000000000000)
      | 1 => orderedInterval (1137686069 / 1000000000000) (1137686273 / 1000000000000)
      | 2 => orderedInterval (721022613 / 1000000000000) (721029166 / 1000000000000)
      | 3 => orderedInterval (5944680174 / 1000000000000) (5944688601 / 1000000000000)
      | 4 => orderedInterval (-4999095415 / 1000000000000) (-4999094955 / 1000000000000)
      | 5 => orderedInterval (10141260892 / 1000000000000) (10141268767 / 1000000000000)
      | 6 => orderedInterval (-2520948875 / 1000000000000) (-2520948762 / 1000000000000)
      | 7 => orderedInterval (-1145690771 / 1000000000000) (-1145690709 / 1000000000000)
      | _ => orderedInterval (-36325306203 / 1000000000000) (-36325276201 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2969292363 / 1000000000000) (2969316670 / 1000000000000)
    | 1 => orderedInterval (-19062300454 / 1000000000000) (-19062271350 / 1000000000000)
    | 2 => orderedInterval (4538922333 / 1000000000000) (4538958239 / 1000000000000)
    | 3 => orderedInterval (49909622017 / 1000000000000) (49909667718 / 1000000000000)
    | _ => orderedInterval (-17858522851 / 1000000000000) (-17858462087 / 1000000000000)

theorem compactCertificate595_stateChecks0 :
    compactCertificate595.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (933 / 2)) (orderedInterval (26811560853 / 1000000000000) (26811578342 / 1000000000000), orderedInterval (-25441582583 / 1000000000000) (-25441565093 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1374487154391633 / 4000000000000)) (orderedInterval (-39604154400 / 1000000000000) (-39604136609 / 1000000000000), orderedInterval (16915437727 / 1000000000000) (16915455518 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (444480905109489 / 800000000000)) (orderedInterval (-10789503898 / 1000000000000) (-10789503897 / 1000000000000), orderedInterval (-32074687806 / 1000000000000) (-32074687805 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_stateChecks1 :
    compactCertificate595.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (401071923631731 / 4000000000000)) (orderedInterval (39672747224 / 1000000000000) (39672747225 / 1000000000000), orderedInterval (68905688247 / 1000000000000) (68905688248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1077335602307607 / 4000000000000)) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2925175731885819 / 4000000000000)) (orderedInterval (-2595194381 / 1000000000000) (-2595194380 / 1000000000000), orderedInterval (-29388768429 / 1000000000000) (-29388768428 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_stateChecks2 :
    compactCertificate595.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2154671204616147 / 4000000000000)) (orderedInterval (-26949852994 / 1000000000000) (-26949824456 / 1000000000000), orderedInterval (21368552493 / 1000000000000) (21368581030 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (3692065834304031 / 4000000000000)) (orderedInterval (4533222451 / 1000000000000) (4533222452 / 1000000000000), orderedInterval (25865798790 / 1000000000000) (25865798791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2719558983073629 / 4000000000000)) (orderedInterval (26552906695 / 1000000000000) (26552964125 / 1000000000000), orderedInterval (-15228067114 / 1000000000000) (-15228009684 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_stateChecks3 :
    compactCertificate595.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 332 12 (4172502846014067 / 4000000000000)) (orderedInterval (19385684421 / 1000000000000) (19385684423 / 1000000000000), orderedInterval (15303949467 / 1000000000000) (15303949469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2408995641340443 / 4000000000000)) (orderedInterval (-4912900934 / 1000000000000) (-4912900933 / 1000000000000), orderedInterval (32143378879 / 1000000000000) (32143378881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 340 12 (4274805039393687 / 4000000000000)) (orderedInterval (23787529259 / 1000000000000) (23787530386 / 1000000000000), orderedInterval (5452216813 / 1000000000000) (5452217940 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_stateChecks4 :
    compactCertificate595.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 318 12 (3994077380926803 / 4000000000000)) (orderedInterval (6933187515 / 1000000000000) (6933187516 / 1000000000000), orderedInterval (24276041502 / 1000000000000) (24276041503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2850362082261699 / 4000000000000)) (orderedInterval (-6936643472 / 1000000000000) (-6936643471 / 1000000000000), orderedInterval (-29068679313 / 1000000000000) (-29068679312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (3232006806922821 / 4000000000000)) (orderedInterval (-27649661702 / 1000000000000) (-27649661276 / 1000000000000), orderedInterval (-4819229413 / 1000000000000) (-4819228988 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_stateChecks5 :
    compactCertificate595.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2694510321964149 / 4000000000000)) (orderedInterval (26349037753 / 1000000000000) (26349086863 / 1000000000000), orderedInterval (-15855890565 / 1000000000000) (-15855841455 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2380681585755129 / 4000000000000)) (orderedInterval (-26546269399 / 1000000000000) (-26546235935 / 1000000000000), orderedInterval (19125666204 / 1000000000000) (19125699667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (690014315073771 / 800000000000)) (orderedInterval (16111723091 / 1000000000000) (16111723346 / 1000000000000), orderedInterval (-21884142453 / 1000000000000) (-21884142198 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_stateChecks6 :
    compactCertificate595.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1908615908957937 / 4000000000000)) (orderedInterval (14795033169 / 1000000000000) (14795033170 / 1000000000000), orderedInterval (33380745599 / 1000000000000) (33380745600 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1617954843366057 / 4000000000000)) (orderedInterval (-331166531 / 1000000000000) (-331166529 / 1000000000000), orderedInterval (-39670476005 / 1000000000000) (-39670476004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1012441016926371 / 4000000000000)) (orderedInterval (27225611239 / 1000000000000) (27225615964 / 1000000000000), orderedInterval (-42172136168 / 1000000000000) (-42172131442 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_stateChecks7 :
    compactCertificate595.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (544494146129757 / 4000000000000)) (orderedInterval (-66282107917 / 1000000000000) (-66282106760 / 1000000000000), orderedInterval (17078959576 / 1000000000000) (17078960733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1478407525940271 / 4000000000000)) (orderedInterval (-13094315317 / 1000000000000) (-13094315210 / 1000000000000), orderedInterval (39400292577 / 1000000000000) (39400292683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2018639083724367 / 4000000000000)) (orderedInterval (12228716101 / 1000000000000) (12228716163 / 1000000000000), orderedInterval (-33357911272 / 1000000000000) (-33357911210 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_stateChecks8 :
    compactCertificate595.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (853558983073629 / 4000000000000)) (orderedInterval (28374782816 / 1000000000000) (28374782817 / 1000000000000), orderedInterval (46605152091 / 1000000000000) (46605152092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (3469669878016509 / 4000000000000)) (orderedInterval (24421744442 / 1000000000000) (24421744455 / 1000000000000), orderedInterval (11712123730 / 1000000000000) (11712123743 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2317578679913331 / 4000000000000)) (orderedInterval (28154550147 / 1000000000000) (28154615606 / 1000000000000), orderedInterval (-17519650390 / 1000000000000) (-17519584931 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_states : ∀ j,
    BesselStateValid (compactCertificate595.point j) (compactCertificate595.state j) :=
  compactCertificate595.statesValid_of_checks3 compactCertificate595_stateChecks0
    compactCertificate595_stateChecks1 compactCertificate595_stateChecks2
    compactCertificate595_stateChecks3 compactCertificate595_stateChecks4
    compactCertificate595_stateChecks5 compactCertificate595_stateChecks6
    compactCertificate595_stateChecks7 compactCertificate595_stateChecks8

theorem compactCertificate595_chunkChecks0_0 :
    compactCertificate595.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (933 / 2) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26811560853 / 1000000000000) (26811578342 / 1000000000000), orderedInterval (-25441582583 / 1000000000000) (-25441565093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1374487154391633 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39604154400 / 1000000000000) (-39604136609 / 1000000000000), orderedInterval (16915437727 / 1000000000000) (16915455518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (444480905109489 / 800000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10789503898 / 1000000000000) (-10789503897 / 1000000000000), orderedInterval (-32074687806 / 1000000000000) (-32074687805 / 1000000000000)))) (orderedInterval (9624989838 / 1000000000000) (9624996968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (401071923631731 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (39672747224 / 1000000000000) (39672747225 / 1000000000000), orderedInterval (68905688247 / 1000000000000) (68905688248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2925175731885819 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2595194381 / 1000000000000) (-2595194380 / 1000000000000), orderedInterval (-29388768429 / 1000000000000) (-29388768428 / 1000000000000)))) (orderedInterval (-349065502 / 1000000000000) (-349065445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2154671204616147 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26949852994 / 1000000000000) (-26949824456 / 1000000000000), orderedInterval (21368552493 / 1000000000000) (21368581030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3692065834304031 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4533222451 / 1000000000000) (4533222452 / 1000000000000), orderedInterval (25865798790 / 1000000000000) (25865798791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2719558983073629 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26552906695 / 1000000000000) (26552964125 / 1000000000000), orderedInterval (-15228067114 / 1000000000000) (-15228009684 / 1000000000000)))) (orderedInterval (501908635 / 1000000000000) (501910049 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks0_1 :
    compactCertificate595.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4172502846014067 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19385684421 / 1000000000000) (19385684423 / 1000000000000), orderedInterval (15303949467 / 1000000000000) (15303949469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2408995641340443 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4912900934 / 1000000000000) (-4912900933 / 1000000000000), orderedInterval (32143378879 / 1000000000000) (32143378881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4274805039393687 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23787529259 / 1000000000000) (23787530386 / 1000000000000), orderedInterval (5452216813 / 1000000000000) (5452217940 / 1000000000000)))) (orderedInterval (-427070242 / 1000000000000) (-427069897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3994077380926803 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6933187515 / 1000000000000) (6933187516 / 1000000000000), orderedInterval (24276041502 / 1000000000000) (24276041503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2850362082261699 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6936643472 / 1000000000000) (-6936643471 / 1000000000000), orderedInterval (-29068679313 / 1000000000000) (-29068679312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3232006806922821 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27649661702 / 1000000000000) (-27649661276 / 1000000000000), orderedInterval (-4819229413 / 1000000000000) (-4819228988 / 1000000000000)))) (orderedInterval (-641191133 / 1000000000000) (-641191075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2694510321964149 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26349037753 / 1000000000000) (26349086863 / 1000000000000), orderedInterval (-15855890565 / 1000000000000) (-15855841455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2380681585755129 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26546269399 / 1000000000000) (-26546235935 / 1000000000000), orderedInterval (19125666204 / 1000000000000) (19125699667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (690014315073771 / 800000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16111723091 / 1000000000000) (16111723346 / 1000000000000), orderedInterval (-21884142453 / 1000000000000) (-21884142198 / 1000000000000)))) (orderedInterval (2235946592 / 1000000000000) (2235949126 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks0_2 :
    compactCertificate595.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1908615908957937 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14795033169 / 1000000000000) (14795033170 / 1000000000000), orderedInterval (33380745599 / 1000000000000) (33380745600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1617954843366057 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-331166531 / 1000000000000) (-331166529 / 1000000000000), orderedInterval (-39670476005 / 1000000000000) (-39670476004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1012441016926371 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27225611239 / 1000000000000) (27225615964 / 1000000000000), orderedInterval (-42172136168 / 1000000000000) (-42172131442 / 1000000000000)))) (orderedInterval (-1460532879 / 1000000000000) (-1460532607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (544494146129757 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66282107917 / 1000000000000) (-66282106760 / 1000000000000), orderedInterval (17078959576 / 1000000000000) (17078960733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1478407525940271 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13094315317 / 1000000000000) (-13094315210 / 1000000000000), orderedInterval (39400292577 / 1000000000000) (39400292683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2018639083724367 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12228716101 / 1000000000000) (12228716163 / 1000000000000), orderedInterval (-33357911272 / 1000000000000) (-33357911210 / 1000000000000)))) (orderedInterval (583780762 / 1000000000000) (583780847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (853558983073629 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28374782816 / 1000000000000) (28374782817 / 1000000000000), orderedInterval (46605152091 / 1000000000000) (46605152092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3469669878016509 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24421744442 / 1000000000000) (24421744455 / 1000000000000), orderedInterval (11712123730 / 1000000000000) (11712123743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2317578679913331 / 4000000000000) 0 (IntervalRat.scale (933 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28154550147 / 1000000000000) (28154615606 / 1000000000000), orderedInterval (-17519650390 / 1000000000000) (-17519584931 / 1000000000000)))) (orderedInterval (-7099473708 / 1000000000000) (-7099461296 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks0 :
    compactCertificate595.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate595.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate595_chunkChecks0_0
    compactCertificate595_chunkChecks0_1 compactCertificate595_chunkChecks0_2

theorem compactCertificate595_chunkChecks1_0 :
    compactCertificate595.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (933 / 2) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26811560853 / 1000000000000) (26811578342 / 1000000000000), orderedInterval (-25441582583 / 1000000000000) (-25441565093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1374487154391633 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39604154400 / 1000000000000) (-39604136609 / 1000000000000), orderedInterval (16915437727 / 1000000000000) (16915455518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (444480905109489 / 800000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10789503898 / 1000000000000) (-10789503897 / 1000000000000), orderedInterval (-32074687806 / 1000000000000) (-32074687805 / 1000000000000)))) (orderedInterval (-12209725226 / 1000000000000) (-12209718135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (401071923631731 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (39672747224 / 1000000000000) (39672747225 / 1000000000000), orderedInterval (68905688247 / 1000000000000) (68905688248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2925175731885819 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2595194381 / 1000000000000) (-2595194380 / 1000000000000), orderedInterval (-29388768429 / 1000000000000) (-29388768428 / 1000000000000)))) (orderedInterval (4137688981 / 1000000000000) (4137689045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2154671204616147 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26949852994 / 1000000000000) (-26949824456 / 1000000000000), orderedInterval (21368552493 / 1000000000000) (21368581030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3692065834304031 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4533222451 / 1000000000000) (4533222452 / 1000000000000), orderedInterval (25865798790 / 1000000000000) (25865798791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2719558983073629 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26552906695 / 1000000000000) (26552964125 / 1000000000000), orderedInterval (-15228067114 / 1000000000000) (-15228009684 / 1000000000000)))) (orderedInterval (-2114915999 / 1000000000000) (-2114913930 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks1_1 :
    compactCertificate595.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4172502846014067 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19385684421 / 1000000000000) (19385684423 / 1000000000000), orderedInterval (15303949467 / 1000000000000) (15303949469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2408995641340443 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4912900934 / 1000000000000) (-4912900933 / 1000000000000), orderedInterval (32143378879 / 1000000000000) (32143378881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4274805039393687 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23787529259 / 1000000000000) (23787530386 / 1000000000000), orderedInterval (5452216813 / 1000000000000) (5452217940 / 1000000000000)))) (orderedInterval (-1230429882 / 1000000000000) (-1230429131 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3994077380926803 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6933187515 / 1000000000000) (6933187516 / 1000000000000), orderedInterval (24276041502 / 1000000000000) (24276041503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2850362082261699 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6936643472 / 1000000000000) (-6936643471 / 1000000000000), orderedInterval (-29068679313 / 1000000000000) (-29068679312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3232006806922821 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27649661702 / 1000000000000) (-27649661276 / 1000000000000), orderedInterval (-4819229413 / 1000000000000) (-4819228988 / 1000000000000)))) (orderedInterval (-5094714589 / 1000000000000) (-5094714495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2694510321964149 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26349037753 / 1000000000000) (26349086863 / 1000000000000), orderedInterval (-15855890565 / 1000000000000) (-15855841455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2380681585755129 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26546269399 / 1000000000000) (-26546235935 / 1000000000000), orderedInterval (19125666204 / 1000000000000) (19125699667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (690014315073771 / 800000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16111723091 / 1000000000000) (16111723346 / 1000000000000), orderedInterval (-21884142453 / 1000000000000) (-21884142198 / 1000000000000)))) (orderedInterval (-2696764984 / 1000000000000) (-2696761644 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks1_2 :
    compactCertificate595.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1908615908957937 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14795033169 / 1000000000000) (14795033170 / 1000000000000), orderedInterval (33380745599 / 1000000000000) (33380745600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1617954843366057 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-331166531 / 1000000000000) (-331166529 / 1000000000000), orderedInterval (-39670476005 / 1000000000000) (-39670476004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1012441016926371 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27225611239 / 1000000000000) (27225615964 / 1000000000000), orderedInterval (-42172136168 / 1000000000000) (-42172131442 / 1000000000000)))) (orderedInterval (-4257259671 / 1000000000000) (-4257259478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (544494146129757 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66282107917 / 1000000000000) (-66282106760 / 1000000000000), orderedInterval (17078959576 / 1000000000000) (17078960733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1478407525940271 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13094315317 / 1000000000000) (-13094315210 / 1000000000000), orderedInterval (39400292577 / 1000000000000) (39400292683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2018639083724367 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12228716101 / 1000000000000) (12228716163 / 1000000000000), orderedInterval (-33357911272 / 1000000000000) (-33357911210 / 1000000000000)))) (orderedInterval (1965412211 / 1000000000000) (1965412275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (853558983073629 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28374782816 / 1000000000000) (28374782817 / 1000000000000), orderedInterval (46605152091 / 1000000000000) (46605152092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3469669878016509 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24421744442 / 1000000000000) (24421744455 / 1000000000000), orderedInterval (11712123730 / 1000000000000) (11712123743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2317578679913331 / 4000000000000) 1 (IntervalRat.scale (933 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28154550147 / 1000000000000) (28154615606 / 1000000000000), orderedInterval (-17519650390 / 1000000000000) (-17519584931 / 1000000000000)))) (orderedInterval (2438408705 / 1000000000000) (2438424143 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks1 :
    compactCertificate595.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate595.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate595_chunkChecks1_0
    compactCertificate595_chunkChecks1_1 compactCertificate595_chunkChecks1_2

theorem compactCertificate595_chunkChecks2_0 :
    compactCertificate595.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (933 / 2) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26811560853 / 1000000000000) (26811578342 / 1000000000000), orderedInterval (-25441582583 / 1000000000000) (-25441565093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1374487154391633 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39604154400 / 1000000000000) (-39604136609 / 1000000000000), orderedInterval (16915437727 / 1000000000000) (16915455518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (444480905109489 / 800000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10789503898 / 1000000000000) (-10789503897 / 1000000000000), orderedInterval (-32074687806 / 1000000000000) (-32074687805 / 1000000000000)))) (orderedInterval (-9502673940 / 1000000000000) (-9502666861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (401071923631731 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (39672747224 / 1000000000000) (39672747225 / 1000000000000), orderedInterval (68905688247 / 1000000000000) (68905688248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2925175731885819 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2595194381 / 1000000000000) (-2595194380 / 1000000000000), orderedInterval (-29388768429 / 1000000000000) (-29388768428 / 1000000000000)))) (orderedInterval (-407980860 / 1000000000000) (-407980772 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2154671204616147 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26949852994 / 1000000000000) (-26949824456 / 1000000000000), orderedInterval (21368552493 / 1000000000000) (21368581030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3692065834304031 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4533222451 / 1000000000000) (4533222452 / 1000000000000), orderedInterval (25865798790 / 1000000000000) (25865798791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2719558983073629 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26552906695 / 1000000000000) (26552964125 / 1000000000000), orderedInterval (-15228067114 / 1000000000000) (-15228009684 / 1000000000000)))) (orderedInterval (-811181454 / 1000000000000) (-811178420 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks2_1 :
    compactCertificate595.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4172502846014067 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19385684421 / 1000000000000) (19385684423 / 1000000000000), orderedInterval (15303949467 / 1000000000000) (15303949469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2408995641340443 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4912900934 / 1000000000000) (-4912900933 / 1000000000000), orderedInterval (32143378879 / 1000000000000) (32143378881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4274805039393687 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23787529259 / 1000000000000) (23787530386 / 1000000000000), orderedInterval (5452216813 / 1000000000000) (5452217940 / 1000000000000)))) (orderedInterval (85379814 / 1000000000000) (85381479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3994077380926803 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6933187515 / 1000000000000) (6933187516 / 1000000000000), orderedInterval (24276041502 / 1000000000000) (24276041503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2850362082261699 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6936643472 / 1000000000000) (-6936643471 / 1000000000000), orderedInterval (-29068679313 / 1000000000000) (-29068679312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3232006806922821 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27649661702 / 1000000000000) (-27649661276 / 1000000000000), orderedInterval (-4819229413 / 1000000000000) (-4819228988 / 1000000000000)))) (orderedInterval (1695146864 / 1000000000000) (1695147021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2694510321964149 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26349037753 / 1000000000000) (26349086863 / 1000000000000), orderedInterval (-15855890565 / 1000000000000) (-15855841455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2380681585755129 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26546269399 / 1000000000000) (-26546235935 / 1000000000000), orderedInterval (19125666204 / 1000000000000) (19125699667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (690014315073771 / 800000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16111723091 / 1000000000000) (16111723346 / 1000000000000), orderedInterval (-21884142453 / 1000000000000) (-21884142198 / 1000000000000)))) (orderedInterval (-4511628155 / 1000000000000) (-4511623730 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks2_2 :
    compactCertificate595.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1908615908957937 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14795033169 / 1000000000000) (14795033170 / 1000000000000), orderedInterval (33380745599 / 1000000000000) (33380745600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1617954843366057 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-331166531 / 1000000000000) (-331166529 / 1000000000000), orderedInterval (-39670476005 / 1000000000000) (-39670476004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1012441016926371 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27225611239 / 1000000000000) (27225615964 / 1000000000000), orderedInterval (-42172136168 / 1000000000000) (-42172131442 / 1000000000000)))) (orderedInterval (2209009345 / 1000000000000) (2209009494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (544494146129757 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66282107917 / 1000000000000) (-66282106760 / 1000000000000), orderedInterval (17078959576 / 1000000000000) (17078960733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1478407525940271 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13094315317 / 1000000000000) (-13094315210 / 1000000000000), orderedInterval (39400292577 / 1000000000000) (39400292683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2018639083724367 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12228716101 / 1000000000000) (12228716163 / 1000000000000), orderedInterval (-33357911272 / 1000000000000) (-33357911210 / 1000000000000)))) (orderedInterval (801892037 / 1000000000000) (801892096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (853558983073629 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28374782816 / 1000000000000) (28374782817 / 1000000000000), orderedInterval (46605152091 / 1000000000000) (46605152092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3469669878016509 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24421744442 / 1000000000000) (24421744455 / 1000000000000), orderedInterval (11712123730 / 1000000000000) (11712123743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2317578679913331 / 4000000000000) 2 (IntervalRat.scale (933 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28154550147 / 1000000000000) (28154615606 / 1000000000000), orderedInterval (-17519650390 / 1000000000000) (-17519584931 / 1000000000000)))) (orderedInterval (14980958682 / 1000000000000) (14980977932 / 1000000000000))) = true
  rfl'

theorem compactCertificate595_chunkChecks2 :
    compactCertificate595.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate595.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate595_chunkChecks2_0
    compactCertificate595_chunkChecks2_1 compactCertificate595_chunkChecks2_2

theorem compactCertificate595_chunkChecks3_0 :
    compactCertificate595.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (933 / 2) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26811560853 / 1000000000000) (26811578342 / 1000000000000), orderedInterval (-25441582583 / 1000000000000) (-25441565093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1374487154391633 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39604154400 / 1000000000000) (-39604136609 / 1000000000000), orderedInterval (16915437727 / 1000000000000) (16915455518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (444480905109489 / 800000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10789503898 / 1000000000000) (-10789503897 / 1000000000000), orderedInterval (-32074687806 / 1000000000000) (-32074687805 / 1000000000000)))) (orderedInterval (13221233936 / 1000000000000) (13221240999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (401071923631731 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (39672747224 / 1000000000000) (39672747225 / 1000000000000), orderedInterval (68905688247 / 1000000000000) (68905688248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2925175731885819 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2595194381 / 1000000000000) (-2595194380 / 1000000000000), orderedInterval (-29388768429 / 1000000000000) (-29388768428 / 1000000000000)))) (orderedInterval (-8381148688 / 1000000000000) (-8381148556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2154671204616147 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26949852994 / 1000000000000) (-26949824456 / 1000000000000), orderedInterval (21368552493 / 1000000000000) (21368581030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3692065834304031 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4533222451 / 1000000000000) (4533222452 / 1000000000000), orderedInterval (25865798790 / 1000000000000) (25865798791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2719558983073629 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26552906695 / 1000000000000) (26552964125 / 1000000000000), orderedInterval (-15228067114 / 1000000000000) (-15228009684 / 1000000000000)))) (orderedInterval (7320783866 / 1000000000000) (7320788316 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate595_chunkChecks3_1 :
    compactCertificate595.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4172502846014067 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19385684421 / 1000000000000) (19385684423 / 1000000000000), orderedInterval (15303949467 / 1000000000000) (15303949469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2408995641340443 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4912900934 / 1000000000000) (-4912900933 / 1000000000000), orderedInterval (32143378879 / 1000000000000) (32143378881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4274805039393687 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23787529259 / 1000000000000) (23787530386 / 1000000000000), orderedInterval (5452216813 / 1000000000000) (5452217940 / 1000000000000)))) (orderedInterval (15959879540 / 1000000000000) (15959883272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3994077380926803 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6933187515 / 1000000000000) (6933187516 / 1000000000000), orderedInterval (24276041502 / 1000000000000) (24276041503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2850362082261699 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6936643472 / 1000000000000) (-6936643471 / 1000000000000), orderedInterval (-29068679313 / 1000000000000) (-29068679312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3232006806922821 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27649661702 / 1000000000000) (-27649661276 / 1000000000000), orderedInterval (-4819229413 / 1000000000000) (-4819228988 / 1000000000000)))) (orderedInterval (13964801044 / 1000000000000) (13964801309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2694510321964149 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26349037753 / 1000000000000) (26349086863 / 1000000000000), orderedInterval (-15855890565 / 1000000000000) (-15855841455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2380681585755129 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26546269399 / 1000000000000) (-26546235935 / 1000000000000), orderedInterval (19125666204 / 1000000000000) (19125699667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (690014315073771 / 800000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16111723091 / 1000000000000) (16111723346 / 1000000000000), orderedInterval (-21884142453 / 1000000000000) (-21884142198 / 1000000000000)))) (orderedInterval (6375367967 / 1000000000000) (6375373850 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate595_chunkChecks3_2 :
    compactCertificate595.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1908615908957937 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14795033169 / 1000000000000) (14795033170 / 1000000000000), orderedInterval (33380745599 / 1000000000000) (33380745600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1617954843366057 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-331166531 / 1000000000000) (-331166529 / 1000000000000), orderedInterval (-39670476005 / 1000000000000) (-39670476004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1012441016926371 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27225611239 / 1000000000000) (27225615964 / 1000000000000), orderedInterval (-42172136168 / 1000000000000) (-42172131442 / 1000000000000)))) (orderedInterval (4462278259 / 1000000000000) (4462278384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (544494146129757 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66282107917 / 1000000000000) (-66282106760 / 1000000000000), orderedInterval (17078959576 / 1000000000000) (17078960733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1478407525940271 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13094315317 / 1000000000000) (-13094315210 / 1000000000000), orderedInterval (39400292577 / 1000000000000) (39400292683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2018639083724367 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12228716101 / 1000000000000) (12228716163 / 1000000000000), orderedInterval (-33357911272 / 1000000000000) (-33357911210 / 1000000000000)))) (orderedInterval (-2785923943 / 1000000000000) (-2785923883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (853558983073629 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28374782816 / 1000000000000) (28374782817 / 1000000000000), orderedInterval (46605152091 / 1000000000000) (46605152092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3469669878016509 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24421744442 / 1000000000000) (24421744455 / 1000000000000), orderedInterval (11712123730 / 1000000000000) (11712123743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2317578679913331 / 4000000000000) 3 (IntervalRat.scale (933 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28154550147 / 1000000000000) (28154615606 / 1000000000000), orderedInterval (-17519650390 / 1000000000000) (-17519584931 / 1000000000000)))) (orderedInterval (-227649964 / 1000000000000) (-227625973 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate595_chunkChecks3 :
    compactCertificate595.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate595.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate595_chunkChecks3_0
    compactCertificate595_chunkChecks3_1 compactCertificate595_chunkChecks3_2

theorem compactCertificate595_chunkChecks4_0 :
    compactCertificate595.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (933 / 2) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26811560853 / 1000000000000) (26811578342 / 1000000000000), orderedInterval (-25441582583 / 1000000000000) (-25441565093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1374487154391633 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39604154400 / 1000000000000) (-39604136609 / 1000000000000), orderedInterval (16915437727 / 1000000000000) (16915455518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (444480905109489 / 800000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10789503898 / 1000000000000) (-10789503897 / 1000000000000), orderedInterval (-32074687806 / 1000000000000) (-32074687805 / 1000000000000)))) (orderedInterval (9187868665 / 1000000000000) (9187875733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (401071923631731 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (39672747224 / 1000000000000) (39672747225 / 1000000000000), orderedInterval (68905688247 / 1000000000000) (68905688248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2925175731885819 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2595194381 / 1000000000000) (-2595194380 / 1000000000000), orderedInterval (-29388768429 / 1000000000000) (-29388768428 / 1000000000000)))) (orderedInterval (1137686069 / 1000000000000) (1137686273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2154671204616147 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26949852994 / 1000000000000) (-26949824456 / 1000000000000), orderedInterval (21368552493 / 1000000000000) (21368581030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3692065834304031 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4533222451 / 1000000000000) (4533222452 / 1000000000000), orderedInterval (25865798790 / 1000000000000) (25865798791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2719558983073629 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26552906695 / 1000000000000) (26552964125 / 1000000000000), orderedInterval (-15228067114 / 1000000000000) (-15228009684 / 1000000000000)))) (orderedInterval (721022613 / 1000000000000) (721029166 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate595_chunkChecks4_1 :
    compactCertificate595.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4172502846014067 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19385684421 / 1000000000000) (19385684423 / 1000000000000), orderedInterval (15303949467 / 1000000000000) (15303949469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2408995641340443 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4912900934 / 1000000000000) (-4912900933 / 1000000000000), orderedInterval (32143378879 / 1000000000000) (32143378881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4274805039393687 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23787529259 / 1000000000000) (23787530386 / 1000000000000), orderedInterval (5452216813 / 1000000000000) (5452217940 / 1000000000000)))) (orderedInterval (5944680174 / 1000000000000) (5944688601 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3994077380926803 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6933187515 / 1000000000000) (6933187516 / 1000000000000), orderedInterval (24276041502 / 1000000000000) (24276041503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2850362082261699 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6936643472 / 1000000000000) (-6936643471 / 1000000000000), orderedInterval (-29068679313 / 1000000000000) (-29068679312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3232006806922821 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27649661702 / 1000000000000) (-27649661276 / 1000000000000), orderedInterval (-4819229413 / 1000000000000) (-4819228988 / 1000000000000)))) (orderedInterval (-4999095415 / 1000000000000) (-4999094955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2694510321964149 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26349037753 / 1000000000000) (26349086863 / 1000000000000), orderedInterval (-15855890565 / 1000000000000) (-15855841455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2380681585755129 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26546269399 / 1000000000000) (-26546235935 / 1000000000000), orderedInterval (19125666204 / 1000000000000) (19125699667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (690014315073771 / 800000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16111723091 / 1000000000000) (16111723346 / 1000000000000), orderedInterval (-21884142453 / 1000000000000) (-21884142198 / 1000000000000)))) (orderedInterval (10141260892 / 1000000000000) (10141268767 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate595_chunkChecks4_2 :
    compactCertificate595.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1908615908957937 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14795033169 / 1000000000000) (14795033170 / 1000000000000), orderedInterval (33380745599 / 1000000000000) (33380745600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1617954843366057 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-331166531 / 1000000000000) (-331166529 / 1000000000000), orderedInterval (-39670476005 / 1000000000000) (-39670476004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1012441016926371 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27225611239 / 1000000000000) (27225615964 / 1000000000000), orderedInterval (-42172136168 / 1000000000000) (-42172131442 / 1000000000000)))) (orderedInterval (-2520948875 / 1000000000000) (-2520948762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (544494146129757 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66282107917 / 1000000000000) (-66282106760 / 1000000000000), orderedInterval (17078959576 / 1000000000000) (17078960733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1478407525940271 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13094315317 / 1000000000000) (-13094315210 / 1000000000000), orderedInterval (39400292577 / 1000000000000) (39400292683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2018639083724367 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12228716101 / 1000000000000) (12228716163 / 1000000000000), orderedInterval (-33357911272 / 1000000000000) (-33357911210 / 1000000000000)))) (orderedInterval (-1145690771 / 1000000000000) (-1145690709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (853558983073629 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (28374782816 / 1000000000000) (28374782817 / 1000000000000), orderedInterval (46605152091 / 1000000000000) (46605152092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3469669878016509 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24421744442 / 1000000000000) (24421744455 / 1000000000000), orderedInterval (11712123730 / 1000000000000) (11712123743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2317578679913331 / 4000000000000) 4 (IntervalRat.scale (933 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28154550147 / 1000000000000) (28154615606 / 1000000000000), orderedInterval (-17519650390 / 1000000000000) (-17519584931 / 1000000000000)))) (orderedInterval (-36325306203 / 1000000000000) (-36325276201 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate595_chunkChecks4 :
    compactCertificate595.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate595.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate595_chunkChecks4_0
    compactCertificate595_chunkChecks4_1 compactCertificate595_chunkChecks4_2

theorem compactCertificate595_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate595.chunkCheck r b = true :=
  compactCertificate595.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate595_chunkChecks0
    · exact compactCertificate595_chunkChecks1
    · exact compactCertificate595_chunkChecks2
    · exact compactCertificate595_chunkChecks3
    · exact compactCertificate595_chunkChecks4)

theorem compactCertificate595_coefficient0 :
    compactCertificate595.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate595_coefficient1 :
    compactCertificate595.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate595_coefficient2 :
    compactCertificate595.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate595_coefficient3 :
    compactCertificate595.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate595_coefficient4 :
    compactCertificate595.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate595_coefficients : ∀ r : Fin 5,
    compactCertificate595.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate595_coefficient0
  · exact compactCertificate595_coefficient1
  · exact compactCertificate595_coefficient2
  · exact compactCertificate595_coefficient3
  · exact compactCertificate595_coefficient4

theorem compactCertificate595_lower : (1 : ℚ) ≤ compactCertificate595.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate595, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate595_proves {t : ℝ} (ht : t ∈ compactCertificate595.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate595.proves compactCertificate595_states compactCertificate595_chunks
    compactCertificate595_coefficients compactCertificate595_lower ht

end Erdos232
