/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate325 : CompactCertificate where
  left := 197
  right := 198
  center := 395 / 2
  grid := fun i =>
    match i.val with
    | 0 => 63
    | 1 => 46
    | 2 => 75
    | 3 => 14
    | 4 => 36
    | 5 => 99
    | 6 => 73
    | 7 => 124
    | 8 => 92
    | 9 => 141
    | 10 => 81
    | 11 => 144
    | 12 => 135
    | 13 => 96
    | 14 => 109
    | 15 => 91
    | 16 => 80
    | 17 => 116
    | 18 => 64
    | 19 => 55
    | 20 => 34
    | 21 => 18
    | 22 => 50
    | 23 => 68
    | 24 => 29
    | 25 => 117
    | _ => 78
  point := fun i =>
    match i.val with
    | 0 => 395 / 2
    | 1 => 116382084884179 / 800000000000
    | 2 => 37635575030707 / 160000000000
    | 3 => 33960002108153 / 800000000000
    | 4 => 91221342531941 / 800000000000
    | 5 => 247683690052497 / 800000000000
    | 6 => 182442685063961 / 800000000000
    | 7 => 312618650493053 / 800000000000
    | 8 => 230273483025527 / 800000000000
    | 9 => 353298740444921 / 800000000000
    | 10 => 203977122900209 / 800000000000
    | 11 => 361960984042981 / 800000000000
    | 12 => 338190903636889 / 800000000000
    | 13 => 241348986600937 / 800000000000
    | 14 => 273664027595823 / 800000000000
    | 15 => 228152535300287 / 800000000000
    | 16 => 201579684110027 / 800000000000
    | 17 => 58425649400673 / 160000000000
    | 18 => 161608421015731 / 800000000000
    | 19 => 136997248259291 / 800000000000
    | 20 => 85726516974473 / 800000000000
    | 21 => 46104005942391 / 800000000000
    | 22 => 125181344640173 / 800000000000
    | 23 => 170924424023821 / 800000000000
    | 24 => 72273483025527 / 800000000000
    | 25 => 293787695994967 / 800000000000
    | _ => 196236565608953 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-20235399562 / 1000000000000) (-20235399561 / 1000000000000), orderedInterval (-52995237535 / 1000000000000) (-52995237534 / 1000000000000))
    | 1 => (orderedInterval (65105427834 / 1000000000000) (65105428354 / 1000000000000), orderedInterval (-11942386252 / 1000000000000) (-11942385732 / 1000000000000))
    | 2 => (orderedInterval (-19671013739 / 1000000000000) (-19671013738 / 1000000000000), orderedInterval (-48119531930 / 1000000000000) (-48119531929 / 1000000000000))
    | 3 => (orderedInterval (-83457631825 / 1000000000000) (-83457563678 / 1000000000000), orderedInterval (90603337777 / 1000000000000) (90603405924 / 1000000000000))
    | 4 => (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708203 / 1000000000000) (-10961707932 / 1000000000000))
    | 5 => (orderedInterval (26644252340 / 1000000000000) (26644258519 / 1000000000000), orderedInterval (-36735255764 / 1000000000000) (-36735249585 / 1000000000000))
    | 6 => (orderedInterval (25240299836 / 1000000000000) (25240302219 / 1000000000000), orderedInterval (-46471603429 / 1000000000000) (-46471601046 / 1000000000000))
    | 7 => (orderedInterval (36686278337 / 1000000000000) (36686307169 / 1000000000000), orderedInterval (-16876781960 / 1000000000000) (-16876753129 / 1000000000000))
    | 8 => (orderedInterval (-18301113380 / 1000000000000) (-18301112857 / 1000000000000), orderedInterval (43353509481 / 1000000000000) (43353510004 / 1000000000000))
    | 9 => (orderedInterval (20039821181 / 1000000000000) (20039822528 / 1000000000000), orderedInterval (-32270950483 / 1000000000000) (-32270949135 / 1000000000000))
    | 10 => (orderedInterval (-47973750682 / 1000000000000) (-47973750680 / 1000000000000), orderedInterval (-13882451242 / 1000000000000) (-13882451240 / 1000000000000))
    | 11 => (orderedInterval (28106829132 / 1000000000000) (28106829133 / 1000000000000), orderedInterval (24809475344 / 1000000000000) (24809475345 / 1000000000000))
    | 12 => (orderedInterval (21631531441 / 1000000000000) (21631533688 / 1000000000000), orderedInterval (-32243888241 / 1000000000000) (-32243885994 / 1000000000000))
    | 13 => (orderedInterval (35356228944 / 1000000000000) (35356228945 / 1000000000000), orderedInterval (29269570761 / 1000000000000) (29269570762 / 1000000000000))
    | 14 => (orderedInterval (-18041178224 / 1000000000000) (-18041178223 / 1000000000000), orderedInterval (-39159635241 / 1000000000000) (-39159635240 / 1000000000000))
    | 15 => (orderedInterval (-4279291389 / 1000000000000) (-4279291388 / 1000000000000), orderedInterval (-47045140505 / 1000000000000) (-47045140504 / 1000000000000))
    | 16 => (orderedInterval (49781764797 / 1000000000000) (49781764810 / 1000000000000), orderedInterval (6850652539 / 1000000000000) (6850652551 / 1000000000000))
    | 17 => (orderedInterval (41701441845 / 1000000000000) (41701441956 / 1000000000000), orderedInterval (2037219107 / 1000000000000) (2037219217 / 1000000000000))
    | 18 => (orderedInterval (55397130882 / 1000000000000) (55397131493 / 1000000000000), orderedInterval (-9223780980 / 1000000000000) (-9223780369 / 1000000000000))
    | 19 => (orderedInterval (41843862433 / 1000000000000) (41843903921 / 1000000000000), orderedInterval (-44469151152 / 1000000000000) (-44469109664 / 1000000000000))
    | 20 => (orderedInterval (69651034034 / 1000000000000) (69651034035 / 1000000000000), orderedInterval (32684548718 / 1000000000000) (32684548719 / 1000000000000))
    | 21 => (orderedInterval (100598447947 / 1000000000000) (100598449196 / 1000000000000), orderedInterval (-31307545905 / 1000000000000) (-31307544657 / 1000000000000))
    | 22 => (orderedInterval (11522654020 / 1000000000000) (11522654021 / 1000000000000), orderedInterval (62698434923 / 1000000000000) (62698434924 / 1000000000000))
    | 23 => (orderedInterval (39612841045 / 1000000000000) (39612841046 / 1000000000000), orderedInterval (37463621070 / 1000000000000) (37463621071 / 1000000000000))
    | 24 => (orderedInterval (-1652042462 / 1000000000000) (-1652042457 / 1000000000000), orderedInterval (-83920382567 / 1000000000000) (-83920382562 / 1000000000000))
    | 25 => (orderedInterval (-18235203110 / 1000000000000) (-18235203109 / 1000000000000), orderedInterval (-37405492835 / 1000000000000) (-37405492834 / 1000000000000))
    | _ => (orderedInterval (43840542976 / 1000000000000) (43840542977 / 1000000000000), orderedInterval (25859043979 / 1000000000000) (25859043980 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8568265241 / 1000000000000) (-8568265222 / 1000000000000)
      | 1 => orderedInterval (1711681460 / 1000000000000) (1711682673 / 1000000000000)
      | 2 => orderedInterval (-1573854303 / 1000000000000) (-1573853389 / 1000000000000)
      | 3 => orderedInterval (-3119743325 / 1000000000000) (-3119743006 / 1000000000000)
      | 4 => orderedInterval (3044169143 / 1000000000000) (3044169208 / 1000000000000)
      | 5 => orderedInterval (-1830539198 / 1000000000000) (-1830539175 / 1000000000000)
      | 6 => orderedInterval (-8958437492 / 1000000000000) (-8958434996 / 1000000000000)
      | 7 => orderedInterval (-5154858383 / 1000000000000) (-5154858336 / 1000000000000)
      | _ => orderedInterval (-6751229965 / 1000000000000) (-6751229909 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-24450460388 / 1000000000000) (-24450460368 / 1000000000000)
      | 1 => orderedInterval (3651475802 / 1000000000000) (3651476683 / 1000000000000)
      | 2 => orderedInterval (2556999615 / 1000000000000) (2557001413 / 1000000000000)
      | 3 => orderedInterval (19573630903 / 1000000000000) (19573631602 / 1000000000000)
      | 4 => orderedInterval (5817106255 / 1000000000000) (5817106381 / 1000000000000)
      | 5 => orderedInterval (-1188203834 / 1000000000000) (-1188203800 / 1000000000000)
      | 6 => orderedInterval (4268196251 / 1000000000000) (4268198433 / 1000000000000)
      | 7 => orderedInterval (-4064317675 / 1000000000000) (-4064317646 / 1000000000000)
      | _ => orderedInterval (-595732073 / 1000000000000) (-595731995 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9452623824 / 1000000000000) (9452623845 / 1000000000000)
      | 1 => orderedInterval (3694249689 / 1000000000000) (3694250848 / 1000000000000)
      | 2 => orderedInterval (5356403191 / 1000000000000) (5356406744 / 1000000000000)
      | 3 => orderedInterval (2659761462 / 1000000000000) (2659763010 / 1000000000000)
      | 4 => orderedInterval (-6315428050 / 1000000000000) (-6315427800 / 1000000000000)
      | 5 => orderedInterval (1096189502 / 1000000000000) (1096189554 / 1000000000000)
      | 6 => orderedInterval (10358214073 / 1000000000000) (10358215996 / 1000000000000)
      | 7 => orderedInterval (3895704850 / 1000000000000) (3895704874 / 1000000000000)
      | _ => orderedInterval (7561634509 / 1000000000000) (7561634624 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (25771837640 / 1000000000000) (25771837664 / 1000000000000)
      | 1 => orderedInterval (-9992113016 / 1000000000000) (-9992111253 / 1000000000000)
      | 2 => orderedInterval (-7302768509 / 1000000000000) (-7302761501 / 1000000000000)
      | 3 => orderedInterval (-104312650551 / 1000000000000) (-104312647103 / 1000000000000)
      | 4 => orderedInterval (-16571098747 / 1000000000000) (-16571098240 / 1000000000000)
      | 5 => orderedInterval (2114616867 / 1000000000000) (2114616950 / 1000000000000)
      | 6 => orderedInterval (-3441215691 / 1000000000000) (-3441214003 / 1000000000000)
      | 7 => orderedInterval (4308192620 / 1000000000000) (4308192643 / 1000000000000)
      | _ => orderedInterval (-10269195009 / 1000000000000) (-10269194833 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10425331074 / 1000000000000) (-10425331047 / 1000000000000)
      | 1 => orderedInterval (-11035304988 / 1000000000000) (-11035302229 / 1000000000000)
      | 2 => orderedInterval (-19263745040 / 1000000000000) (-19263731168 / 1000000000000)
      | 3 => orderedInterval (12213391811 / 1000000000000) (12213399519 / 1000000000000)
      | 4 => orderedInterval (10995155987 / 1000000000000) (10995157030 / 1000000000000)
      | 5 => orderedInterval (4693233104 / 1000000000000) (4693233240 / 1000000000000)
      | 6 => orderedInterval (-10801918049 / 1000000000000) (-10801916556 / 1000000000000)
      | 7 => orderedInterval (-4317890849 / 1000000000000) (-4317890826 / 1000000000000)
      | _ => orderedInterval (-1725477537 / 1000000000000) (-1725477254 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-31201077304 / 1000000000000) (-31201072152 / 1000000000000)
    | 1 => orderedInterval (5568694856 / 1000000000000) (5568700703 / 1000000000000)
    | 2 => orderedInterval (37759353050 / 1000000000000) (37759361695 / 1000000000000)
    | 3 => orderedInterval (-119694394396 / 1000000000000) (-119694379676 / 1000000000000)
    | _ => orderedInterval (-29667886635 / 1000000000000) (-29667859291 / 1000000000000)

theorem compactCertificate325_stateChecks0 :
    compactCertificate325.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (395 / 2)) (orderedInterval (-20235399562 / 1000000000000) (-20235399561 / 1000000000000), orderedInterval (-52995237535 / 1000000000000) (-52995237534 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (116382084884179 / 800000000000)) (orderedInterval (65105427834 / 1000000000000) (65105428354 / 1000000000000), orderedInterval (-11942386252 / 1000000000000) (-11942385732 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (37635575030707 / 160000000000)) (orderedInterval (-19671013739 / 1000000000000) (-19671013738 / 1000000000000), orderedInterval (-48119531930 / 1000000000000) (-48119531929 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_stateChecks1 :
    compactCertificate325.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (33960002108153 / 800000000000)) (orderedInterval (-83457631825 / 1000000000000) (-83457563678 / 1000000000000), orderedInterval (90603337777 / 1000000000000) (90603405924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (91221342531941 / 800000000000)) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708203 / 1000000000000) (-10961707932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (247683690052497 / 800000000000)) (orderedInterval (26644252340 / 1000000000000) (26644258519 / 1000000000000), orderedInterval (-36735255764 / 1000000000000) (-36735249585 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_stateChecks2 :
    compactCertificate325.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (182442685063961 / 800000000000)) (orderedInterval (25240299836 / 1000000000000) (25240302219 / 1000000000000), orderedInterval (-46471603429 / 1000000000000) (-46471601046 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (312618650493053 / 800000000000)) (orderedInterval (36686278337 / 1000000000000) (36686307169 / 1000000000000), orderedInterval (-16876781960 / 1000000000000) (-16876753129 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (230273483025527 / 800000000000)) (orderedInterval (-18301113380 / 1000000000000) (-18301112857 / 1000000000000), orderedInterval (43353509481 / 1000000000000) (43353510004 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_stateChecks3 :
    compactCertificate325.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (353298740444921 / 800000000000)) (orderedInterval (20039821181 / 1000000000000) (20039822528 / 1000000000000), orderedInterval (-32270950483 / 1000000000000) (-32270949135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (203977122900209 / 800000000000)) (orderedInterval (-47973750682 / 1000000000000) (-47973750680 / 1000000000000), orderedInterval (-13882451242 / 1000000000000) (-13882451240 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (361960984042981 / 800000000000)) (orderedInterval (28106829132 / 1000000000000) (28106829133 / 1000000000000), orderedInterval (24809475344 / 1000000000000) (24809475345 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_stateChecks4 :
    compactCertificate325.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (338190903636889 / 800000000000)) (orderedInterval (21631531441 / 1000000000000) (21631533688 / 1000000000000), orderedInterval (-32243888241 / 1000000000000) (-32243885994 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (241348986600937 / 800000000000)) (orderedInterval (35356228944 / 1000000000000) (35356228945 / 1000000000000), orderedInterval (29269570761 / 1000000000000) (29269570762 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (273664027595823 / 800000000000)) (orderedInterval (-18041178224 / 1000000000000) (-18041178223 / 1000000000000), orderedInterval (-39159635241 / 1000000000000) (-39159635240 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_stateChecks5 :
    compactCertificate325.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (228152535300287 / 800000000000)) (orderedInterval (-4279291389 / 1000000000000) (-4279291388 / 1000000000000), orderedInterval (-47045140505 / 1000000000000) (-47045140504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201579684110027 / 800000000000)) (orderedInterval (49781764797 / 1000000000000) (49781764810 / 1000000000000), orderedInterval (6850652539 / 1000000000000) (6850652551 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (58425649400673 / 160000000000)) (orderedInterval (41701441845 / 1000000000000) (41701441956 / 1000000000000), orderedInterval (2037219107 / 1000000000000) (2037219217 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_stateChecks6 :
    compactCertificate325.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (161608421015731 / 800000000000)) (orderedInterval (55397130882 / 1000000000000) (55397131493 / 1000000000000), orderedInterval (-9223780980 / 1000000000000) (-9223780369 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (136997248259291 / 800000000000)) (orderedInterval (41843862433 / 1000000000000) (41843903921 / 1000000000000), orderedInterval (-44469151152 / 1000000000000) (-44469109664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (85726516974473 / 800000000000)) (orderedInterval (69651034034 / 1000000000000) (69651034035 / 1000000000000), orderedInterval (32684548718 / 1000000000000) (32684548719 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_stateChecks7 :
    compactCertificate325.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (46104005942391 / 800000000000)) (orderedInterval (100598447947 / 1000000000000) (100598449196 / 1000000000000), orderedInterval (-31307545905 / 1000000000000) (-31307544657 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (125181344640173 / 800000000000)) (orderedInterval (11522654020 / 1000000000000) (11522654021 / 1000000000000), orderedInterval (62698434923 / 1000000000000) (62698434924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (170924424023821 / 800000000000)) (orderedInterval (39612841045 / 1000000000000) (39612841046 / 1000000000000), orderedInterval (37463621070 / 1000000000000) (37463621071 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_stateChecks8 :
    compactCertificate325.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (72273483025527 / 800000000000)) (orderedInterval (-1652042462 / 1000000000000) (-1652042457 / 1000000000000), orderedInterval (-83920382567 / 1000000000000) (-83920382562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (293787695994967 / 800000000000)) (orderedInterval (-18235203110 / 1000000000000) (-18235203109 / 1000000000000), orderedInterval (-37405492835 / 1000000000000) (-37405492834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (196236565608953 / 800000000000)) (orderedInterval (43840542976 / 1000000000000) (43840542977 / 1000000000000), orderedInterval (25859043979 / 1000000000000) (25859043980 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_states : ∀ j,
    BesselStateValid (compactCertificate325.point j) (compactCertificate325.state j) :=
  compactCertificate325.statesValid_of_checks3 compactCertificate325_stateChecks0
    compactCertificate325_stateChecks1 compactCertificate325_stateChecks2
    compactCertificate325_stateChecks3 compactCertificate325_stateChecks4
    compactCertificate325_stateChecks5 compactCertificate325_stateChecks6
    compactCertificate325_stateChecks7 compactCertificate325_stateChecks8

theorem compactCertificate325_chunkChecks0_0 :
    compactCertificate325.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (395 / 2) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-20235399562 / 1000000000000) (-20235399561 / 1000000000000), orderedInterval (-52995237535 / 1000000000000) (-52995237534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (116382084884179 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65105427834 / 1000000000000) (65105428354 / 1000000000000), orderedInterval (-11942386252 / 1000000000000) (-11942385732 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (37635575030707 / 160000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19671013739 / 1000000000000) (-19671013738 / 1000000000000), orderedInterval (-48119531930 / 1000000000000) (-48119531929 / 1000000000000)))) (orderedInterval (-8568265241 / 1000000000000) (-8568265222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (33960002108153 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83457631825 / 1000000000000) (-83457563678 / 1000000000000), orderedInterval (90603337777 / 1000000000000) (90603405924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (91221342531941 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708203 / 1000000000000) (-10961707932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (247683690052497 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26644252340 / 1000000000000) (26644258519 / 1000000000000), orderedInterval (-36735255764 / 1000000000000) (-36735249585 / 1000000000000)))) (orderedInterval (1711681460 / 1000000000000) (1711682673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (182442685063961 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25240299836 / 1000000000000) (25240302219 / 1000000000000), orderedInterval (-46471603429 / 1000000000000) (-46471601046 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (312618650493053 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36686278337 / 1000000000000) (36686307169 / 1000000000000), orderedInterval (-16876781960 / 1000000000000) (-16876753129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (230273483025527 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18301113380 / 1000000000000) (-18301112857 / 1000000000000), orderedInterval (43353509481 / 1000000000000) (43353510004 / 1000000000000)))) (orderedInterval (-1573854303 / 1000000000000) (-1573853389 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks0_1 :
    compactCertificate325.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (353298740444921 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20039821181 / 1000000000000) (20039822528 / 1000000000000), orderedInterval (-32270950483 / 1000000000000) (-32270949135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (203977122900209 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47973750682 / 1000000000000) (-47973750680 / 1000000000000), orderedInterval (-13882451242 / 1000000000000) (-13882451240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (361960984042981 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28106829132 / 1000000000000) (28106829133 / 1000000000000), orderedInterval (24809475344 / 1000000000000) (24809475345 / 1000000000000)))) (orderedInterval (-3119743325 / 1000000000000) (-3119743006 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (338190903636889 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21631531441 / 1000000000000) (21631533688 / 1000000000000), orderedInterval (-32243888241 / 1000000000000) (-32243885994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (241348986600937 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35356228944 / 1000000000000) (35356228945 / 1000000000000), orderedInterval (29269570761 / 1000000000000) (29269570762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (273664027595823 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-18041178224 / 1000000000000) (-18041178223 / 1000000000000), orderedInterval (-39159635241 / 1000000000000) (-39159635240 / 1000000000000)))) (orderedInterval (3044169143 / 1000000000000) (3044169208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (228152535300287 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4279291389 / 1000000000000) (-4279291388 / 1000000000000), orderedInterval (-47045140505 / 1000000000000) (-47045140504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (201579684110027 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49781764797 / 1000000000000) (49781764810 / 1000000000000), orderedInterval (6850652539 / 1000000000000) (6850652551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (58425649400673 / 160000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (41701441845 / 1000000000000) (41701441956 / 1000000000000), orderedInterval (2037219107 / 1000000000000) (2037219217 / 1000000000000)))) (orderedInterval (-1830539198 / 1000000000000) (-1830539175 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks0_2 :
    compactCertificate325.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (161608421015731 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55397130882 / 1000000000000) (55397131493 / 1000000000000), orderedInterval (-9223780980 / 1000000000000) (-9223780369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (136997248259291 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41843862433 / 1000000000000) (41843903921 / 1000000000000), orderedInterval (-44469151152 / 1000000000000) (-44469109664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (85726516974473 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69651034034 / 1000000000000) (69651034035 / 1000000000000), orderedInterval (32684548718 / 1000000000000) (32684548719 / 1000000000000)))) (orderedInterval (-8958437492 / 1000000000000) (-8958434996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (46104005942391 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100598447947 / 1000000000000) (100598449196 / 1000000000000), orderedInterval (-31307545905 / 1000000000000) (-31307544657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (125181344640173 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11522654020 / 1000000000000) (11522654021 / 1000000000000), orderedInterval (62698434923 / 1000000000000) (62698434924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (170924424023821 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39612841045 / 1000000000000) (39612841046 / 1000000000000), orderedInterval (37463621070 / 1000000000000) (37463621071 / 1000000000000)))) (orderedInterval (-5154858383 / 1000000000000) (-5154858336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (72273483025527 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1652042462 / 1000000000000) (-1652042457 / 1000000000000), orderedInterval (-83920382567 / 1000000000000) (-83920382562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (293787695994967 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18235203110 / 1000000000000) (-18235203109 / 1000000000000), orderedInterval (-37405492835 / 1000000000000) (-37405492834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (196236565608953 / 800000000000) 0 (IntervalRat.scale (395 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43840542976 / 1000000000000) (43840542977 / 1000000000000), orderedInterval (25859043979 / 1000000000000) (25859043980 / 1000000000000)))) (orderedInterval (-6751229965 / 1000000000000) (-6751229909 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks0 :
    compactCertificate325.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate325.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate325_chunkChecks0_0
    compactCertificate325_chunkChecks0_1 compactCertificate325_chunkChecks0_2

theorem compactCertificate325_chunkChecks1_0 :
    compactCertificate325.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (395 / 2) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-20235399562 / 1000000000000) (-20235399561 / 1000000000000), orderedInterval (-52995237535 / 1000000000000) (-52995237534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (116382084884179 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65105427834 / 1000000000000) (65105428354 / 1000000000000), orderedInterval (-11942386252 / 1000000000000) (-11942385732 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (37635575030707 / 160000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19671013739 / 1000000000000) (-19671013738 / 1000000000000), orderedInterval (-48119531930 / 1000000000000) (-48119531929 / 1000000000000)))) (orderedInterval (-24450460388 / 1000000000000) (-24450460368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (33960002108153 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83457631825 / 1000000000000) (-83457563678 / 1000000000000), orderedInterval (90603337777 / 1000000000000) (90603405924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (91221342531941 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708203 / 1000000000000) (-10961707932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (247683690052497 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26644252340 / 1000000000000) (26644258519 / 1000000000000), orderedInterval (-36735255764 / 1000000000000) (-36735249585 / 1000000000000)))) (orderedInterval (3651475802 / 1000000000000) (3651476683 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (182442685063961 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25240299836 / 1000000000000) (25240302219 / 1000000000000), orderedInterval (-46471603429 / 1000000000000) (-46471601046 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (312618650493053 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36686278337 / 1000000000000) (36686307169 / 1000000000000), orderedInterval (-16876781960 / 1000000000000) (-16876753129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (230273483025527 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18301113380 / 1000000000000) (-18301112857 / 1000000000000), orderedInterval (43353509481 / 1000000000000) (43353510004 / 1000000000000)))) (orderedInterval (2556999615 / 1000000000000) (2557001413 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks1_1 :
    compactCertificate325.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (353298740444921 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20039821181 / 1000000000000) (20039822528 / 1000000000000), orderedInterval (-32270950483 / 1000000000000) (-32270949135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (203977122900209 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47973750682 / 1000000000000) (-47973750680 / 1000000000000), orderedInterval (-13882451242 / 1000000000000) (-13882451240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (361960984042981 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28106829132 / 1000000000000) (28106829133 / 1000000000000), orderedInterval (24809475344 / 1000000000000) (24809475345 / 1000000000000)))) (orderedInterval (19573630903 / 1000000000000) (19573631602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (338190903636889 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21631531441 / 1000000000000) (21631533688 / 1000000000000), orderedInterval (-32243888241 / 1000000000000) (-32243885994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (241348986600937 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35356228944 / 1000000000000) (35356228945 / 1000000000000), orderedInterval (29269570761 / 1000000000000) (29269570762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (273664027595823 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-18041178224 / 1000000000000) (-18041178223 / 1000000000000), orderedInterval (-39159635241 / 1000000000000) (-39159635240 / 1000000000000)))) (orderedInterval (5817106255 / 1000000000000) (5817106381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (228152535300287 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4279291389 / 1000000000000) (-4279291388 / 1000000000000), orderedInterval (-47045140505 / 1000000000000) (-47045140504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (201579684110027 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49781764797 / 1000000000000) (49781764810 / 1000000000000), orderedInterval (6850652539 / 1000000000000) (6850652551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (58425649400673 / 160000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (41701441845 / 1000000000000) (41701441956 / 1000000000000), orderedInterval (2037219107 / 1000000000000) (2037219217 / 1000000000000)))) (orderedInterval (-1188203834 / 1000000000000) (-1188203800 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks1_2 :
    compactCertificate325.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (161608421015731 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55397130882 / 1000000000000) (55397131493 / 1000000000000), orderedInterval (-9223780980 / 1000000000000) (-9223780369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (136997248259291 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41843862433 / 1000000000000) (41843903921 / 1000000000000), orderedInterval (-44469151152 / 1000000000000) (-44469109664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (85726516974473 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69651034034 / 1000000000000) (69651034035 / 1000000000000), orderedInterval (32684548718 / 1000000000000) (32684548719 / 1000000000000)))) (orderedInterval (4268196251 / 1000000000000) (4268198433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (46104005942391 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100598447947 / 1000000000000) (100598449196 / 1000000000000), orderedInterval (-31307545905 / 1000000000000) (-31307544657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (125181344640173 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11522654020 / 1000000000000) (11522654021 / 1000000000000), orderedInterval (62698434923 / 1000000000000) (62698434924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (170924424023821 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39612841045 / 1000000000000) (39612841046 / 1000000000000), orderedInterval (37463621070 / 1000000000000) (37463621071 / 1000000000000)))) (orderedInterval (-4064317675 / 1000000000000) (-4064317646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (72273483025527 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1652042462 / 1000000000000) (-1652042457 / 1000000000000), orderedInterval (-83920382567 / 1000000000000) (-83920382562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (293787695994967 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18235203110 / 1000000000000) (-18235203109 / 1000000000000), orderedInterval (-37405492835 / 1000000000000) (-37405492834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (196236565608953 / 800000000000) 1 (IntervalRat.scale (395 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43840542976 / 1000000000000) (43840542977 / 1000000000000), orderedInterval (25859043979 / 1000000000000) (25859043980 / 1000000000000)))) (orderedInterval (-595732073 / 1000000000000) (-595731995 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks1 :
    compactCertificate325.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate325.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate325_chunkChecks1_0
    compactCertificate325_chunkChecks1_1 compactCertificate325_chunkChecks1_2

theorem compactCertificate325_chunkChecks2_0 :
    compactCertificate325.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (395 / 2) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-20235399562 / 1000000000000) (-20235399561 / 1000000000000), orderedInterval (-52995237535 / 1000000000000) (-52995237534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (116382084884179 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65105427834 / 1000000000000) (65105428354 / 1000000000000), orderedInterval (-11942386252 / 1000000000000) (-11942385732 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (37635575030707 / 160000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19671013739 / 1000000000000) (-19671013738 / 1000000000000), orderedInterval (-48119531930 / 1000000000000) (-48119531929 / 1000000000000)))) (orderedInterval (9452623824 / 1000000000000) (9452623845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (33960002108153 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83457631825 / 1000000000000) (-83457563678 / 1000000000000), orderedInterval (90603337777 / 1000000000000) (90603405924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (91221342531941 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708203 / 1000000000000) (-10961707932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (247683690052497 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26644252340 / 1000000000000) (26644258519 / 1000000000000), orderedInterval (-36735255764 / 1000000000000) (-36735249585 / 1000000000000)))) (orderedInterval (3694249689 / 1000000000000) (3694250848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (182442685063961 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25240299836 / 1000000000000) (25240302219 / 1000000000000), orderedInterval (-46471603429 / 1000000000000) (-46471601046 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (312618650493053 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36686278337 / 1000000000000) (36686307169 / 1000000000000), orderedInterval (-16876781960 / 1000000000000) (-16876753129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (230273483025527 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18301113380 / 1000000000000) (-18301112857 / 1000000000000), orderedInterval (43353509481 / 1000000000000) (43353510004 / 1000000000000)))) (orderedInterval (5356403191 / 1000000000000) (5356406744 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks2_1 :
    compactCertificate325.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (353298740444921 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20039821181 / 1000000000000) (20039822528 / 1000000000000), orderedInterval (-32270950483 / 1000000000000) (-32270949135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (203977122900209 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47973750682 / 1000000000000) (-47973750680 / 1000000000000), orderedInterval (-13882451242 / 1000000000000) (-13882451240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (361960984042981 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28106829132 / 1000000000000) (28106829133 / 1000000000000), orderedInterval (24809475344 / 1000000000000) (24809475345 / 1000000000000)))) (orderedInterval (2659761462 / 1000000000000) (2659763010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (338190903636889 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21631531441 / 1000000000000) (21631533688 / 1000000000000), orderedInterval (-32243888241 / 1000000000000) (-32243885994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (241348986600937 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35356228944 / 1000000000000) (35356228945 / 1000000000000), orderedInterval (29269570761 / 1000000000000) (29269570762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (273664027595823 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-18041178224 / 1000000000000) (-18041178223 / 1000000000000), orderedInterval (-39159635241 / 1000000000000) (-39159635240 / 1000000000000)))) (orderedInterval (-6315428050 / 1000000000000) (-6315427800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (228152535300287 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4279291389 / 1000000000000) (-4279291388 / 1000000000000), orderedInterval (-47045140505 / 1000000000000) (-47045140504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (201579684110027 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49781764797 / 1000000000000) (49781764810 / 1000000000000), orderedInterval (6850652539 / 1000000000000) (6850652551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (58425649400673 / 160000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (41701441845 / 1000000000000) (41701441956 / 1000000000000), orderedInterval (2037219107 / 1000000000000) (2037219217 / 1000000000000)))) (orderedInterval (1096189502 / 1000000000000) (1096189554 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks2_2 :
    compactCertificate325.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (161608421015731 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55397130882 / 1000000000000) (55397131493 / 1000000000000), orderedInterval (-9223780980 / 1000000000000) (-9223780369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (136997248259291 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41843862433 / 1000000000000) (41843903921 / 1000000000000), orderedInterval (-44469151152 / 1000000000000) (-44469109664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (85726516974473 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69651034034 / 1000000000000) (69651034035 / 1000000000000), orderedInterval (32684548718 / 1000000000000) (32684548719 / 1000000000000)))) (orderedInterval (10358214073 / 1000000000000) (10358215996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (46104005942391 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100598447947 / 1000000000000) (100598449196 / 1000000000000), orderedInterval (-31307545905 / 1000000000000) (-31307544657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (125181344640173 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11522654020 / 1000000000000) (11522654021 / 1000000000000), orderedInterval (62698434923 / 1000000000000) (62698434924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (170924424023821 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39612841045 / 1000000000000) (39612841046 / 1000000000000), orderedInterval (37463621070 / 1000000000000) (37463621071 / 1000000000000)))) (orderedInterval (3895704850 / 1000000000000) (3895704874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (72273483025527 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1652042462 / 1000000000000) (-1652042457 / 1000000000000), orderedInterval (-83920382567 / 1000000000000) (-83920382562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (293787695994967 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18235203110 / 1000000000000) (-18235203109 / 1000000000000), orderedInterval (-37405492835 / 1000000000000) (-37405492834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (196236565608953 / 800000000000) 2 (IntervalRat.scale (395 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43840542976 / 1000000000000) (43840542977 / 1000000000000), orderedInterval (25859043979 / 1000000000000) (25859043980 / 1000000000000)))) (orderedInterval (7561634509 / 1000000000000) (7561634624 / 1000000000000))) = true
  rfl'

theorem compactCertificate325_chunkChecks2 :
    compactCertificate325.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate325.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate325_chunkChecks2_0
    compactCertificate325_chunkChecks2_1 compactCertificate325_chunkChecks2_2

theorem compactCertificate325_chunkChecks3_0 :
    compactCertificate325.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (395 / 2) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-20235399562 / 1000000000000) (-20235399561 / 1000000000000), orderedInterval (-52995237535 / 1000000000000) (-52995237534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (116382084884179 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65105427834 / 1000000000000) (65105428354 / 1000000000000), orderedInterval (-11942386252 / 1000000000000) (-11942385732 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (37635575030707 / 160000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19671013739 / 1000000000000) (-19671013738 / 1000000000000), orderedInterval (-48119531930 / 1000000000000) (-48119531929 / 1000000000000)))) (orderedInterval (25771837640 / 1000000000000) (25771837664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (33960002108153 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83457631825 / 1000000000000) (-83457563678 / 1000000000000), orderedInterval (90603337777 / 1000000000000) (90603405924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (91221342531941 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708203 / 1000000000000) (-10961707932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (247683690052497 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26644252340 / 1000000000000) (26644258519 / 1000000000000), orderedInterval (-36735255764 / 1000000000000) (-36735249585 / 1000000000000)))) (orderedInterval (-9992113016 / 1000000000000) (-9992111253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (182442685063961 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25240299836 / 1000000000000) (25240302219 / 1000000000000), orderedInterval (-46471603429 / 1000000000000) (-46471601046 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (312618650493053 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36686278337 / 1000000000000) (36686307169 / 1000000000000), orderedInterval (-16876781960 / 1000000000000) (-16876753129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (230273483025527 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18301113380 / 1000000000000) (-18301112857 / 1000000000000), orderedInterval (43353509481 / 1000000000000) (43353510004 / 1000000000000)))) (orderedInterval (-7302768509 / 1000000000000) (-7302761501 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate325_chunkChecks3_1 :
    compactCertificate325.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (353298740444921 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20039821181 / 1000000000000) (20039822528 / 1000000000000), orderedInterval (-32270950483 / 1000000000000) (-32270949135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (203977122900209 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47973750682 / 1000000000000) (-47973750680 / 1000000000000), orderedInterval (-13882451242 / 1000000000000) (-13882451240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (361960984042981 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28106829132 / 1000000000000) (28106829133 / 1000000000000), orderedInterval (24809475344 / 1000000000000) (24809475345 / 1000000000000)))) (orderedInterval (-104312650551 / 1000000000000) (-104312647103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (338190903636889 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21631531441 / 1000000000000) (21631533688 / 1000000000000), orderedInterval (-32243888241 / 1000000000000) (-32243885994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (241348986600937 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35356228944 / 1000000000000) (35356228945 / 1000000000000), orderedInterval (29269570761 / 1000000000000) (29269570762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (273664027595823 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-18041178224 / 1000000000000) (-18041178223 / 1000000000000), orderedInterval (-39159635241 / 1000000000000) (-39159635240 / 1000000000000)))) (orderedInterval (-16571098747 / 1000000000000) (-16571098240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (228152535300287 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4279291389 / 1000000000000) (-4279291388 / 1000000000000), orderedInterval (-47045140505 / 1000000000000) (-47045140504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (201579684110027 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49781764797 / 1000000000000) (49781764810 / 1000000000000), orderedInterval (6850652539 / 1000000000000) (6850652551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (58425649400673 / 160000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (41701441845 / 1000000000000) (41701441956 / 1000000000000), orderedInterval (2037219107 / 1000000000000) (2037219217 / 1000000000000)))) (orderedInterval (2114616867 / 1000000000000) (2114616950 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate325_chunkChecks3_2 :
    compactCertificate325.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (161608421015731 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55397130882 / 1000000000000) (55397131493 / 1000000000000), orderedInterval (-9223780980 / 1000000000000) (-9223780369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (136997248259291 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41843862433 / 1000000000000) (41843903921 / 1000000000000), orderedInterval (-44469151152 / 1000000000000) (-44469109664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (85726516974473 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69651034034 / 1000000000000) (69651034035 / 1000000000000), orderedInterval (32684548718 / 1000000000000) (32684548719 / 1000000000000)))) (orderedInterval (-3441215691 / 1000000000000) (-3441214003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (46104005942391 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100598447947 / 1000000000000) (100598449196 / 1000000000000), orderedInterval (-31307545905 / 1000000000000) (-31307544657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (125181344640173 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11522654020 / 1000000000000) (11522654021 / 1000000000000), orderedInterval (62698434923 / 1000000000000) (62698434924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (170924424023821 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39612841045 / 1000000000000) (39612841046 / 1000000000000), orderedInterval (37463621070 / 1000000000000) (37463621071 / 1000000000000)))) (orderedInterval (4308192620 / 1000000000000) (4308192643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (72273483025527 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1652042462 / 1000000000000) (-1652042457 / 1000000000000), orderedInterval (-83920382567 / 1000000000000) (-83920382562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (293787695994967 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18235203110 / 1000000000000) (-18235203109 / 1000000000000), orderedInterval (-37405492835 / 1000000000000) (-37405492834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (196236565608953 / 800000000000) 3 (IntervalRat.scale (395 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43840542976 / 1000000000000) (43840542977 / 1000000000000), orderedInterval (25859043979 / 1000000000000) (25859043980 / 1000000000000)))) (orderedInterval (-10269195009 / 1000000000000) (-10269194833 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate325_chunkChecks3 :
    compactCertificate325.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate325.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate325_chunkChecks3_0
    compactCertificate325_chunkChecks3_1 compactCertificate325_chunkChecks3_2

theorem compactCertificate325_chunkChecks4_0 :
    compactCertificate325.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (395 / 2) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-20235399562 / 1000000000000) (-20235399561 / 1000000000000), orderedInterval (-52995237535 / 1000000000000) (-52995237534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (116382084884179 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65105427834 / 1000000000000) (65105428354 / 1000000000000), orderedInterval (-11942386252 / 1000000000000) (-11942385732 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (37635575030707 / 160000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-19671013739 / 1000000000000) (-19671013738 / 1000000000000), orderedInterval (-48119531930 / 1000000000000) (-48119531929 / 1000000000000)))) (orderedInterval (-10425331074 / 1000000000000) (-10425331047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (33960002108153 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83457631825 / 1000000000000) (-83457563678 / 1000000000000), orderedInterval (90603337777 / 1000000000000) (90603405924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (91221342531941 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (73958578995 / 1000000000000) (73958579266 / 1000000000000), orderedInterval (-10961708203 / 1000000000000) (-10961707932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (247683690052497 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26644252340 / 1000000000000) (26644258519 / 1000000000000), orderedInterval (-36735255764 / 1000000000000) (-36735249585 / 1000000000000)))) (orderedInterval (-11035304988 / 1000000000000) (-11035302229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (182442685063961 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25240299836 / 1000000000000) (25240302219 / 1000000000000), orderedInterval (-46471603429 / 1000000000000) (-46471601046 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (312618650493053 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36686278337 / 1000000000000) (36686307169 / 1000000000000), orderedInterval (-16876781960 / 1000000000000) (-16876753129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (230273483025527 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18301113380 / 1000000000000) (-18301112857 / 1000000000000), orderedInterval (43353509481 / 1000000000000) (43353510004 / 1000000000000)))) (orderedInterval (-19263745040 / 1000000000000) (-19263731168 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate325_chunkChecks4_1 :
    compactCertificate325.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (353298740444921 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20039821181 / 1000000000000) (20039822528 / 1000000000000), orderedInterval (-32270950483 / 1000000000000) (-32270949135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (203977122900209 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-47973750682 / 1000000000000) (-47973750680 / 1000000000000), orderedInterval (-13882451242 / 1000000000000) (-13882451240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (361960984042981 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28106829132 / 1000000000000) (28106829133 / 1000000000000), orderedInterval (24809475344 / 1000000000000) (24809475345 / 1000000000000)))) (orderedInterval (12213391811 / 1000000000000) (12213399519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (338190903636889 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21631531441 / 1000000000000) (21631533688 / 1000000000000), orderedInterval (-32243888241 / 1000000000000) (-32243885994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (241348986600937 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35356228944 / 1000000000000) (35356228945 / 1000000000000), orderedInterval (29269570761 / 1000000000000) (29269570762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (273664027595823 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-18041178224 / 1000000000000) (-18041178223 / 1000000000000), orderedInterval (-39159635241 / 1000000000000) (-39159635240 / 1000000000000)))) (orderedInterval (10995155987 / 1000000000000) (10995157030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (228152535300287 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4279291389 / 1000000000000) (-4279291388 / 1000000000000), orderedInterval (-47045140505 / 1000000000000) (-47045140504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (201579684110027 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49781764797 / 1000000000000) (49781764810 / 1000000000000), orderedInterval (6850652539 / 1000000000000) (6850652551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (58425649400673 / 160000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (41701441845 / 1000000000000) (41701441956 / 1000000000000), orderedInterval (2037219107 / 1000000000000) (2037219217 / 1000000000000)))) (orderedInterval (4693233104 / 1000000000000) (4693233240 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate325_chunkChecks4_2 :
    compactCertificate325.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (161608421015731 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55397130882 / 1000000000000) (55397131493 / 1000000000000), orderedInterval (-9223780980 / 1000000000000) (-9223780369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (136997248259291 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41843862433 / 1000000000000) (41843903921 / 1000000000000), orderedInterval (-44469151152 / 1000000000000) (-44469109664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (85726516974473 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69651034034 / 1000000000000) (69651034035 / 1000000000000), orderedInterval (32684548718 / 1000000000000) (32684548719 / 1000000000000)))) (orderedInterval (-10801918049 / 1000000000000) (-10801916556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (46104005942391 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100598447947 / 1000000000000) (100598449196 / 1000000000000), orderedInterval (-31307545905 / 1000000000000) (-31307544657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (125181344640173 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11522654020 / 1000000000000) (11522654021 / 1000000000000), orderedInterval (62698434923 / 1000000000000) (62698434924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (170924424023821 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39612841045 / 1000000000000) (39612841046 / 1000000000000), orderedInterval (37463621070 / 1000000000000) (37463621071 / 1000000000000)))) (orderedInterval (-4317890849 / 1000000000000) (-4317890826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (72273483025527 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1652042462 / 1000000000000) (-1652042457 / 1000000000000), orderedInterval (-83920382567 / 1000000000000) (-83920382562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (293787695994967 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18235203110 / 1000000000000) (-18235203109 / 1000000000000), orderedInterval (-37405492835 / 1000000000000) (-37405492834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (196236565608953 / 800000000000) 4 (IntervalRat.scale (395 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43840542976 / 1000000000000) (43840542977 / 1000000000000), orderedInterval (25859043979 / 1000000000000) (25859043980 / 1000000000000)))) (orderedInterval (-1725477537 / 1000000000000) (-1725477254 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate325_chunkChecks4 :
    compactCertificate325.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate325.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate325_chunkChecks4_0
    compactCertificate325_chunkChecks4_1 compactCertificate325_chunkChecks4_2

theorem compactCertificate325_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate325.chunkCheck r b = true :=
  compactCertificate325.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate325_chunkChecks0
    · exact compactCertificate325_chunkChecks1
    · exact compactCertificate325_chunkChecks2
    · exact compactCertificate325_chunkChecks3
    · exact compactCertificate325_chunkChecks4)

theorem compactCertificate325_coefficient0 :
    compactCertificate325.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate325_coefficient1 :
    compactCertificate325.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate325_coefficient2 :
    compactCertificate325.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate325_coefficient3 :
    compactCertificate325.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate325_coefficient4 :
    compactCertificate325.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate325_coefficients : ∀ r : Fin 5,
    compactCertificate325.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate325_coefficient0
  · exact compactCertificate325_coefficient1
  · exact compactCertificate325_coefficient2
  · exact compactCertificate325_coefficient3
  · exact compactCertificate325_coefficient4

theorem compactCertificate325_lower : (1 : ℚ) ≤ compactCertificate325.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate325, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate325_proves {t : ℝ} (ht : t ∈ compactCertificate325.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate325.proves compactCertificate325_states compactCertificate325_chunks
    compactCertificate325_coefficients compactCertificate325_lower ht

end Erdos232
