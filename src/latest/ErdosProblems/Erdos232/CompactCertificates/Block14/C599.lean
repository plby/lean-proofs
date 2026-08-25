/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate599 : CompactCertificate where
  left := 470
  right := 471
  center := 941 / 2
  grid := fun i =>
    match i.val with
    | 0 => 150
    | 1 => 110
    | 2 => 178
    | 3 => 32
    | 4 => 87
    | 5 => 235
    | 6 => 173
    | 7 => 296
    | 8 => 218
    | 9 => 335
    | 10 => 193
    | 11 => 343
    | 12 => 321
    | 13 => 229
    | 14 => 260
    | 15 => 216
    | 16 => 191
    | 17 => 277
    | 18 => 153
    | 19 => 130
    | 20 => 81
    | 21 => 44
    | 22 => 119
    | 23 => 162
    | 24 => 69
    | 25 => 279
    | _ => 186
  point := fun i =>
    match i.val with
    | 0 => 941 / 2
    | 1 => 1386272681974841 / 4000000000000
    | 2 => 448292102580953 / 800000000000
    | 3 => 404510911186987 / 4000000000000
    | 4 => 1086573206614639 / 4000000000000
    | 5 => 2950257624549363 / 4000000000000
    | 6 => 2173146413230219 / 4000000000000
    | 7 => 3723723419164087 / 4000000000000
    | 8 => 2742877816797733 / 4000000000000
    | 9 => 4208279933654059 / 4000000000000
    | 10 => 2429651552520211 / 4000000000000
    | 11 => 4311459316258799 / 4000000000000
    | 12 => 4028324561041931 / 4000000000000
    | 13 => 2874802485968123 / 4000000000000
    | 14 => 3259719619843917 / 4000000000000
    | 15 => 2717614376171773 / 4000000000000
    | 16 => 2401094718323233 / 4000000000000
    | 17 => 695930836532067 / 800000000000
    | 18 => 1924981318681049 / 4000000000000
    | 19 => 1631827982430289 / 4000000000000
    | 20 => 1021122183202267 / 4000000000000
    | 21 => 549162906225189 / 4000000000000
    | 22 => 1491084117802567 / 4000000000000
    | 23 => 2035947886157159 / 4000000000000
    | 24 => 860877816797733 / 4000000000000
    | 25 => 3499420530775493 / 4000000000000
    | _ => 2337450737190187 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (1700086779 / 1000000000000) (1700086780 / 1000000000000), orderedInterval (36743004964 / 1000000000000) (36743004965 / 1000000000000))
    | 1 => (orderedInterval (41942438061 / 1000000000000) (41942440485 / 1000000000000), orderedInterval (-8878399535 / 1000000000000) (-8878397111 / 1000000000000))
    | 2 => (orderedInterval (31350925922 / 1000000000000) (31350964430 / 1000000000000), orderedInterval (-12405316730 / 1000000000000) (-12405278223 / 1000000000000))
    | 3 => (orderedInterval (77915953790 / 1000000000000) (77915953792 / 1000000000000), orderedInterval (14589340523 / 1000000000000) (14589340525 / 1000000000000))
    | 4 => (orderedInterval (37628226675 / 1000000000000) (37628312262 / 1000000000000), orderedInterval (-30527463491 / 1000000000000) (-30527377904 / 1000000000000))
    | 5 => (orderedInterval (-2211957904 / 1000000000000) (-2211957903 / 1000000000000), orderedInterval (-29294324619 / 1000000000000) (-29294324618 / 1000000000000))
    | 6 => (orderedInterval (-18651934438 / 1000000000000) (-18651934437 / 1000000000000), orderedInterval (-28686477807 / 1000000000000) (-28686477806 / 1000000000000))
    | 7 => (orderedInterval (25438485406 / 1000000000000) (25438543138 / 1000000000000), orderedInterval (-6074613616 / 1000000000000) (-6074555884 / 1000000000000))
    | 8 => (orderedInterval (30401896730 / 1000000000000) (30401900147 / 1000000000000), orderedInterval (-2052233852 / 1000000000000) (-2052230435 / 1000000000000))
    | 9 => (orderedInterval (-10069209359 / 1000000000000) (-10069209358 / 1000000000000), orderedInterval (-22438981830 / 1000000000000) (-22438981829 / 1000000000000))
    | 10 => (orderedInterval (-30929127899 / 1000000000000) (-30929104038 / 1000000000000), orderedInterval (9589627766 / 1000000000000) (9589651627 / 1000000000000))
    | 11 => (orderedInterval (-21477848131 / 1000000000000) (-21477848094 / 1000000000000), orderedInterval (-11362478974 / 1000000000000) (-11362478937 / 1000000000000))
    | 12 => (orderedInterval (13880035901 / 1000000000000) (13880035946 / 1000000000000), orderedInterval (-20970862929 / 1000000000000) (-20970862884 / 1000000000000))
    | 13 => (orderedInterval (-1818176754 / 1000000000000) (-1818176753 / 1000000000000), orderedInterval (-29705420500 / 1000000000000) (-29705420499 / 1000000000000))
    | 14 => (orderedInterval (-24895708920 / 1000000000000) (-24895660809 / 1000000000000), orderedInterval (12719600128 / 1000000000000) (12719648239 / 1000000000000))
    | 15 => (orderedInterval (30593207635 / 1000000000000) (30593209938 / 1000000000000), orderedInterval (-1063047033 / 1000000000000) (-1063044729 / 1000000000000))
    | 16 => (orderedInterval (-27658616242 / 1000000000000) (-27658616241 / 1000000000000), orderedInterval (-17168529017 / 1000000000000) (-17168529016 / 1000000000000))
    | 17 => (orderedInterval (-12435343887 / 1000000000000) (-12435343886 / 1000000000000), orderedInterval (-24017462425 / 1000000000000) (-24017462424 / 1000000000000))
    | 18 => (orderedInterval (-35616899984 / 1000000000000) (-35616899956 / 1000000000000), orderedInterval (-7331502378 / 1000000000000) (-7331502350 / 1000000000000))
    | 19 => (orderedInterval (12989028915 / 1000000000000) (12989028916 / 1000000000000), orderedInterval (37290823880 / 1000000000000) (37290823881 / 1000000000000))
    | 20 => (orderedInterval (-49921528037 / 1000000000000) (-49921527891 / 1000000000000), orderedInterval (1378699877 / 1000000000000) (1378700023 / 1000000000000))
    | 21 => (orderedInterval (-10503328895 / 1000000000000) (-10503328842 / 1000000000000), orderedInterval (67319220986 / 1000000000000) (67319221039 / 1000000000000))
    | 22 => (orderedInterval (11953033059 / 1000000000000) (11953033129 / 1000000000000), orderedInterval (-39575229548 / 1000000000000) (-39575229478 / 1000000000000))
    | 23 => (orderedInterval (26195697968 / 1000000000000) (26195697969 / 1000000000000), orderedInterval (23734398002 / 1000000000000) (23734398003 / 1000000000000))
    | 24 => (orderedInterval (37689681398 / 1000000000000) (37689718348 / 1000000000000), orderedInterval (-39298414911 / 1000000000000) (-39298377961 / 1000000000000))
    | 25 => (orderedInterval (20512872399 / 1000000000000) (20512876022 / 1000000000000), orderedInterval (-17530512517 / 1000000000000) (-17530508894 / 1000000000000))
    | _ => (orderedInterval (23943321287 / 1000000000000) (23943321288 / 1000000000000), orderedInterval (22698296813 / 1000000000000) (22698296814 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (2904385095 / 1000000000000) (2904387411 / 1000000000000)
      | 1 => orderedInterval (685786663 / 1000000000000) (685789845 / 1000000000000)
      | 2 => orderedInterval (-49872602 / 1000000000000) (-49870712 / 1000000000000)
      | 3 => orderedInterval (-3555619687 / 1000000000000) (-3555617727 / 1000000000000)
      | 4 => orderedInterval (-296523132 / 1000000000000) (-296522831 / 1000000000000)
      | 5 => orderedInterval (1617697018 / 1000000000000) (1617697090 / 1000000000000)
      | 6 => orderedInterval (3334485712 / 1000000000000) (3334485840 / 1000000000000)
      | 7 => orderedInterval (-2084840337 / 1000000000000) (-2084840277 / 1000000000000)
      | _ => orderedInterval (-5934981081 / 1000000000000) (-5934980433 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13635705186 / 1000000000000) (13635707932 / 1000000000000)
      | 1 => orderedInterval (2587059146 / 1000000000000) (2587061015 / 1000000000000)
      | 2 => orderedInterval (298431318 / 1000000000000) (298435008 / 1000000000000)
      | 3 => orderedInterval (6132426434 / 1000000000000) (6132429115 / 1000000000000)
      | 4 => orderedInterval (-3592003818 / 1000000000000) (-3592003303 / 1000000000000)
      | 5 => orderedInterval (98790930 / 1000000000000) (98791034 / 1000000000000)
      | 6 => orderedInterval (-606715020 / 1000000000000) (-606714903 / 1000000000000)
      | 7 => orderedInterval (-1619145932 / 1000000000000) (-1619145880 / 1000000000000)
      | _ => orderedInterval (-2744400912 / 1000000000000) (-2744400078 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3524476428 / 1000000000000) (-3524473162 / 1000000000000)
      | 1 => orderedInterval (-810828288 / 1000000000000) (-810827153 / 1000000000000)
      | 2 => orderedInterval (1510370583 / 1000000000000) (1510377819 / 1000000000000)
      | 3 => orderedInterval (10884181402 / 1000000000000) (10884185210 / 1000000000000)
      | 4 => orderedInterval (1178875125 / 1000000000000) (1178876011 / 1000000000000)
      | 5 => orderedInterval (-2224798489 / 1000000000000) (-2224798336 / 1000000000000)
      | 6 => orderedInterval (-4925520239 / 1000000000000) (-4925520129 / 1000000000000)
      | 7 => orderedInterval (2506637963 / 1000000000000) (2506638015 / 1000000000000)
      | _ => orderedInterval (12661307592 / 1000000000000) (12661308930 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13293210937 / 1000000000000) (-13293207054 / 1000000000000)
      | 1 => orderedInterval (-7804706402 / 1000000000000) (-7804705665 / 1000000000000)
      | 2 => orderedInterval (-1300985241 / 1000000000000) (-1300971028 / 1000000000000)
      | 3 => orderedInterval (-26709304013 / 1000000000000) (-26709298322 / 1000000000000)
      | 4 => orderedInterval (6631326982 / 1000000000000) (6631328512 / 1000000000000)
      | 5 => orderedInterval (1888081581 / 1000000000000) (1888081810 / 1000000000000)
      | 6 => orderedInterval (124766357 / 1000000000000) (124766464 / 1000000000000)
      | 7 => orderedInterval (1881889289 / 1000000000000) (1881889342 / 1000000000000)
      | _ => orderedInterval (-1018874715 / 1000000000000) (-1018872378 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (4547043196 / 1000000000000) (4547047823 / 1000000000000)
      | 1 => orderedInterval (1133628988 / 1000000000000) (1133629543 / 1000000000000)
      | 2 => orderedInterval (-8704670032 / 1000000000000) (-8704642034 / 1000000000000)
      | 3 => orderedInterval (-45618336049 / 1000000000000) (-45618326942 / 1000000000000)
      | 4 => orderedInterval (-5090085040 / 1000000000000) (-5090082382 / 1000000000000)
      | 5 => orderedInterval (2000822775 / 1000000000000) (2000823128 / 1000000000000)
      | 6 => orderedInterval (5676271767 / 1000000000000) (5676271872 / 1000000000000)
      | 7 => orderedInterval (-2863019595 / 1000000000000) (-2863019539 / 1000000000000)
      | _ => orderedInterval (-30635750021 / 1000000000000) (-30635745808 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3379482351 / 1000000000000) (-3379471794 / 1000000000000)
    | 1 => orderedInterval (14190147332 / 1000000000000) (14190159940 / 1000000000000)
    | 2 => orderedInterval (17255749221 / 1000000000000) (17255767205 / 1000000000000)
    | 3 => orderedInterval (-39601017099 / 1000000000000) (-39600988319 / 1000000000000)
    | _ => orderedInterval (-79554094011 / 1000000000000) (-79554044339 / 1000000000000)

theorem compactCertificate599_stateChecks0 :
    compactCertificate599.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (941 / 2)) (orderedInterval (1700086779 / 1000000000000) (1700086780 / 1000000000000), orderedInterval (36743004964 / 1000000000000) (36743004965 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1386272681974841 / 4000000000000)) (orderedInterval (41942438061 / 1000000000000) (41942440485 / 1000000000000), orderedInterval (-8878399535 / 1000000000000) (-8878397111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (448292102580953 / 800000000000)) (orderedInterval (31350925922 / 1000000000000) (31350964430 / 1000000000000), orderedInterval (-12405316730 / 1000000000000) (-12405278223 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_stateChecks1 :
    compactCertificate599.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (404510911186987 / 4000000000000)) (orderedInterval (77915953790 / 1000000000000) (77915953792 / 1000000000000), orderedInterval (14589340523 / 1000000000000) (14589340525 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1086573206614639 / 4000000000000)) (orderedInterval (37628226675 / 1000000000000) (37628312262 / 1000000000000), orderedInterval (-30527463491 / 1000000000000) (-30527377904 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2950257624549363 / 4000000000000)) (orderedInterval (-2211957904 / 1000000000000) (-2211957903 / 1000000000000), orderedInterval (-29294324619 / 1000000000000) (-29294324618 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_stateChecks2 :
    compactCertificate599.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2173146413230219 / 4000000000000)) (orderedInterval (-18651934438 / 1000000000000) (-18651934437 / 1000000000000), orderedInterval (-28686477807 / 1000000000000) (-28686477806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 296 12 (3723723419164087 / 4000000000000)) (orderedInterval (25438485406 / 1000000000000) (25438543138 / 1000000000000), orderedInterval (-6074613616 / 1000000000000) (-6074555884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2742877816797733 / 4000000000000)) (orderedInterval (30401896730 / 1000000000000) (30401900147 / 1000000000000), orderedInterval (-2052233852 / 1000000000000) (-2052230435 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_stateChecks3 :
    compactCertificate599.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 335 12 (4208279933654059 / 4000000000000)) (orderedInterval (-10069209359 / 1000000000000) (-10069209358 / 1000000000000), orderedInterval (-22438981830 / 1000000000000) (-22438981829 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2429651552520211 / 4000000000000)) (orderedInterval (-30929127899 / 1000000000000) (-30929104038 / 1000000000000), orderedInterval (9589627766 / 1000000000000) (9589651627 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 343 12 (4311459316258799 / 4000000000000)) (orderedInterval (-21477848131 / 1000000000000) (-21477848094 / 1000000000000), orderedInterval (-11362478974 / 1000000000000) (-11362478937 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_stateChecks4 :
    compactCertificate599.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 321 12 (4028324561041931 / 4000000000000)) (orderedInterval (13880035901 / 1000000000000) (13880035946 / 1000000000000), orderedInterval (-20970862929 / 1000000000000) (-20970862884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2874802485968123 / 4000000000000)) (orderedInterval (-1818176754 / 1000000000000) (-1818176753 / 1000000000000), orderedInterval (-29705420500 / 1000000000000) (-29705420499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (3259719619843917 / 4000000000000)) (orderedInterval (-24895708920 / 1000000000000) (-24895660809 / 1000000000000), orderedInterval (12719600128 / 1000000000000) (12719648239 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_stateChecks5 :
    compactCertificate599.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2717614376171773 / 4000000000000)) (orderedInterval (30593207635 / 1000000000000) (30593209938 / 1000000000000), orderedInterval (-1063047033 / 1000000000000) (-1063044729 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2401094718323233 / 4000000000000)) (orderedInterval (-27658616242 / 1000000000000) (-27658616241 / 1000000000000), orderedInterval (-17168529017 / 1000000000000) (-17168529016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 277 12 (695930836532067 / 800000000000)) (orderedInterval (-12435343887 / 1000000000000) (-12435343886 / 1000000000000), orderedInterval (-24017462425 / 1000000000000) (-24017462424 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_stateChecks6 :
    compactCertificate599.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1924981318681049 / 4000000000000)) (orderedInterval (-35616899984 / 1000000000000) (-35616899956 / 1000000000000), orderedInterval (-7331502378 / 1000000000000) (-7331502350 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1631827982430289 / 4000000000000)) (orderedInterval (12989028915 / 1000000000000) (12989028916 / 1000000000000), orderedInterval (37290823880 / 1000000000000) (37290823881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1021122183202267 / 4000000000000)) (orderedInterval (-49921528037 / 1000000000000) (-49921527891 / 1000000000000), orderedInterval (1378699877 / 1000000000000) (1378700023 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_stateChecks7 :
    compactCertificate599.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (549162906225189 / 4000000000000)) (orderedInterval (-10503328895 / 1000000000000) (-10503328842 / 1000000000000), orderedInterval (67319220986 / 1000000000000) (67319221039 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1491084117802567 / 4000000000000)) (orderedInterval (11953033059 / 1000000000000) (11953033129 / 1000000000000), orderedInterval (-39575229548 / 1000000000000) (-39575229478 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2035947886157159 / 4000000000000)) (orderedInterval (26195697968 / 1000000000000) (26195697969 / 1000000000000), orderedInterval (23734398002 / 1000000000000) (23734398003 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_stateChecks8 :
    compactCertificate599.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (860877816797733 / 4000000000000)) (orderedInterval (37689681398 / 1000000000000) (37689718348 / 1000000000000), orderedInterval (-39298414911 / 1000000000000) (-39298377961 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (3499420530775493 / 4000000000000)) (orderedInterval (20512872399 / 1000000000000) (20512876022 / 1000000000000), orderedInterval (-17530512517 / 1000000000000) (-17530508894 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2337450737190187 / 4000000000000)) (orderedInterval (23943321287 / 1000000000000) (23943321288 / 1000000000000), orderedInterval (22698296813 / 1000000000000) (22698296814 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_states : ∀ j,
    BesselStateValid (compactCertificate599.point j) (compactCertificate599.state j) :=
  compactCertificate599.statesValid_of_checks3 compactCertificate599_stateChecks0
    compactCertificate599_stateChecks1 compactCertificate599_stateChecks2
    compactCertificate599_stateChecks3 compactCertificate599_stateChecks4
    compactCertificate599_stateChecks5 compactCertificate599_stateChecks6
    compactCertificate599_stateChecks7 compactCertificate599_stateChecks8

theorem compactCertificate599_chunkChecks0_0 :
    compactCertificate599.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (941 / 2) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1700086779 / 1000000000000) (1700086780 / 1000000000000), orderedInterval (36743004964 / 1000000000000) (36743004965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1386272681974841 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41942438061 / 1000000000000) (41942440485 / 1000000000000), orderedInterval (-8878399535 / 1000000000000) (-8878397111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (448292102580953 / 800000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31350925922 / 1000000000000) (31350964430 / 1000000000000), orderedInterval (-12405316730 / 1000000000000) (-12405278223 / 1000000000000)))) (orderedInterval (2904385095 / 1000000000000) (2904387411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (404510911186987 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (77915953790 / 1000000000000) (77915953792 / 1000000000000), orderedInterval (14589340523 / 1000000000000) (14589340525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1086573206614639 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37628226675 / 1000000000000) (37628312262 / 1000000000000), orderedInterval (-30527463491 / 1000000000000) (-30527377904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2950257624549363 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2211957904 / 1000000000000) (-2211957903 / 1000000000000), orderedInterval (-29294324619 / 1000000000000) (-29294324618 / 1000000000000)))) (orderedInterval (685786663 / 1000000000000) (685789845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2173146413230219 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18651934438 / 1000000000000) (-18651934437 / 1000000000000), orderedInterval (-28686477807 / 1000000000000) (-28686477806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3723723419164087 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25438485406 / 1000000000000) (25438543138 / 1000000000000), orderedInterval (-6074613616 / 1000000000000) (-6074555884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2742877816797733 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30401896730 / 1000000000000) (30401900147 / 1000000000000), orderedInterval (-2052233852 / 1000000000000) (-2052230435 / 1000000000000)))) (orderedInterval (-49872602 / 1000000000000) (-49870712 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks0_1 :
    compactCertificate599.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4208279933654059 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10069209359 / 1000000000000) (-10069209358 / 1000000000000), orderedInterval (-22438981830 / 1000000000000) (-22438981829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2429651552520211 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30929127899 / 1000000000000) (-30929104038 / 1000000000000), orderedInterval (9589627766 / 1000000000000) (9589651627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4311459316258799 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21477848131 / 1000000000000) (-21477848094 / 1000000000000), orderedInterval (-11362478974 / 1000000000000) (-11362478937 / 1000000000000)))) (orderedInterval (-3555619687 / 1000000000000) (-3555617727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4028324561041931 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13880035901 / 1000000000000) (13880035946 / 1000000000000), orderedInterval (-20970862929 / 1000000000000) (-20970862884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2874802485968123 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1818176754 / 1000000000000) (-1818176753 / 1000000000000), orderedInterval (-29705420500 / 1000000000000) (-29705420499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3259719619843917 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24895708920 / 1000000000000) (-24895660809 / 1000000000000), orderedInterval (12719600128 / 1000000000000) (12719648239 / 1000000000000)))) (orderedInterval (-296523132 / 1000000000000) (-296522831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2717614376171773 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30593207635 / 1000000000000) (30593209938 / 1000000000000), orderedInterval (-1063047033 / 1000000000000) (-1063044729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2401094718323233 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27658616242 / 1000000000000) (-27658616241 / 1000000000000), orderedInterval (-17168529017 / 1000000000000) (-17168529016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (695930836532067 / 800000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12435343887 / 1000000000000) (-12435343886 / 1000000000000), orderedInterval (-24017462425 / 1000000000000) (-24017462424 / 1000000000000)))) (orderedInterval (1617697018 / 1000000000000) (1617697090 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks0_2 :
    compactCertificate599.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1924981318681049 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35616899984 / 1000000000000) (-35616899956 / 1000000000000), orderedInterval (-7331502378 / 1000000000000) (-7331502350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1631827982430289 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12989028915 / 1000000000000) (12989028916 / 1000000000000), orderedInterval (37290823880 / 1000000000000) (37290823881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1021122183202267 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49921528037 / 1000000000000) (-49921527891 / 1000000000000), orderedInterval (1378699877 / 1000000000000) (1378700023 / 1000000000000)))) (orderedInterval (3334485712 / 1000000000000) (3334485840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (549162906225189 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10503328895 / 1000000000000) (-10503328842 / 1000000000000), orderedInterval (67319220986 / 1000000000000) (67319221039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1491084117802567 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11953033059 / 1000000000000) (11953033129 / 1000000000000), orderedInterval (-39575229548 / 1000000000000) (-39575229478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2035947886157159 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26195697968 / 1000000000000) (26195697969 / 1000000000000), orderedInterval (23734398002 / 1000000000000) (23734398003 / 1000000000000)))) (orderedInterval (-2084840337 / 1000000000000) (-2084840277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (860877816797733 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37689681398 / 1000000000000) (37689718348 / 1000000000000), orderedInterval (-39298414911 / 1000000000000) (-39298377961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3499420530775493 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20512872399 / 1000000000000) (20512876022 / 1000000000000), orderedInterval (-17530512517 / 1000000000000) (-17530508894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2337450737190187 / 4000000000000) 0 (IntervalRat.scale (941 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23943321287 / 1000000000000) (23943321288 / 1000000000000), orderedInterval (22698296813 / 1000000000000) (22698296814 / 1000000000000)))) (orderedInterval (-5934981081 / 1000000000000) (-5934980433 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks0 :
    compactCertificate599.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate599.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate599_chunkChecks0_0
    compactCertificate599_chunkChecks0_1 compactCertificate599_chunkChecks0_2

theorem compactCertificate599_chunkChecks1_0 :
    compactCertificate599.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (941 / 2) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1700086779 / 1000000000000) (1700086780 / 1000000000000), orderedInterval (36743004964 / 1000000000000) (36743004965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1386272681974841 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41942438061 / 1000000000000) (41942440485 / 1000000000000), orderedInterval (-8878399535 / 1000000000000) (-8878397111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (448292102580953 / 800000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31350925922 / 1000000000000) (31350964430 / 1000000000000), orderedInterval (-12405316730 / 1000000000000) (-12405278223 / 1000000000000)))) (orderedInterval (13635705186 / 1000000000000) (13635707932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (404510911186987 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (77915953790 / 1000000000000) (77915953792 / 1000000000000), orderedInterval (14589340523 / 1000000000000) (14589340525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1086573206614639 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37628226675 / 1000000000000) (37628312262 / 1000000000000), orderedInterval (-30527463491 / 1000000000000) (-30527377904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2950257624549363 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2211957904 / 1000000000000) (-2211957903 / 1000000000000), orderedInterval (-29294324619 / 1000000000000) (-29294324618 / 1000000000000)))) (orderedInterval (2587059146 / 1000000000000) (2587061015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2173146413230219 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18651934438 / 1000000000000) (-18651934437 / 1000000000000), orderedInterval (-28686477807 / 1000000000000) (-28686477806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3723723419164087 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25438485406 / 1000000000000) (25438543138 / 1000000000000), orderedInterval (-6074613616 / 1000000000000) (-6074555884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2742877816797733 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30401896730 / 1000000000000) (30401900147 / 1000000000000), orderedInterval (-2052233852 / 1000000000000) (-2052230435 / 1000000000000)))) (orderedInterval (298431318 / 1000000000000) (298435008 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks1_1 :
    compactCertificate599.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4208279933654059 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10069209359 / 1000000000000) (-10069209358 / 1000000000000), orderedInterval (-22438981830 / 1000000000000) (-22438981829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2429651552520211 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30929127899 / 1000000000000) (-30929104038 / 1000000000000), orderedInterval (9589627766 / 1000000000000) (9589651627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4311459316258799 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21477848131 / 1000000000000) (-21477848094 / 1000000000000), orderedInterval (-11362478974 / 1000000000000) (-11362478937 / 1000000000000)))) (orderedInterval (6132426434 / 1000000000000) (6132429115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4028324561041931 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13880035901 / 1000000000000) (13880035946 / 1000000000000), orderedInterval (-20970862929 / 1000000000000) (-20970862884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2874802485968123 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1818176754 / 1000000000000) (-1818176753 / 1000000000000), orderedInterval (-29705420500 / 1000000000000) (-29705420499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3259719619843917 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24895708920 / 1000000000000) (-24895660809 / 1000000000000), orderedInterval (12719600128 / 1000000000000) (12719648239 / 1000000000000)))) (orderedInterval (-3592003818 / 1000000000000) (-3592003303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2717614376171773 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30593207635 / 1000000000000) (30593209938 / 1000000000000), orderedInterval (-1063047033 / 1000000000000) (-1063044729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2401094718323233 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27658616242 / 1000000000000) (-27658616241 / 1000000000000), orderedInterval (-17168529017 / 1000000000000) (-17168529016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (695930836532067 / 800000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12435343887 / 1000000000000) (-12435343886 / 1000000000000), orderedInterval (-24017462425 / 1000000000000) (-24017462424 / 1000000000000)))) (orderedInterval (98790930 / 1000000000000) (98791034 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks1_2 :
    compactCertificate599.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1924981318681049 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35616899984 / 1000000000000) (-35616899956 / 1000000000000), orderedInterval (-7331502378 / 1000000000000) (-7331502350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1631827982430289 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12989028915 / 1000000000000) (12989028916 / 1000000000000), orderedInterval (37290823880 / 1000000000000) (37290823881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1021122183202267 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49921528037 / 1000000000000) (-49921527891 / 1000000000000), orderedInterval (1378699877 / 1000000000000) (1378700023 / 1000000000000)))) (orderedInterval (-606715020 / 1000000000000) (-606714903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (549162906225189 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10503328895 / 1000000000000) (-10503328842 / 1000000000000), orderedInterval (67319220986 / 1000000000000) (67319221039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1491084117802567 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11953033059 / 1000000000000) (11953033129 / 1000000000000), orderedInterval (-39575229548 / 1000000000000) (-39575229478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2035947886157159 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26195697968 / 1000000000000) (26195697969 / 1000000000000), orderedInterval (23734398002 / 1000000000000) (23734398003 / 1000000000000)))) (orderedInterval (-1619145932 / 1000000000000) (-1619145880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (860877816797733 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37689681398 / 1000000000000) (37689718348 / 1000000000000), orderedInterval (-39298414911 / 1000000000000) (-39298377961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3499420530775493 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20512872399 / 1000000000000) (20512876022 / 1000000000000), orderedInterval (-17530512517 / 1000000000000) (-17530508894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2337450737190187 / 4000000000000) 1 (IntervalRat.scale (941 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23943321287 / 1000000000000) (23943321288 / 1000000000000), orderedInterval (22698296813 / 1000000000000) (22698296814 / 1000000000000)))) (orderedInterval (-2744400912 / 1000000000000) (-2744400078 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks1 :
    compactCertificate599.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate599.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate599_chunkChecks1_0
    compactCertificate599_chunkChecks1_1 compactCertificate599_chunkChecks1_2

theorem compactCertificate599_chunkChecks2_0 :
    compactCertificate599.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (941 / 2) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1700086779 / 1000000000000) (1700086780 / 1000000000000), orderedInterval (36743004964 / 1000000000000) (36743004965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1386272681974841 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41942438061 / 1000000000000) (41942440485 / 1000000000000), orderedInterval (-8878399535 / 1000000000000) (-8878397111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (448292102580953 / 800000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31350925922 / 1000000000000) (31350964430 / 1000000000000), orderedInterval (-12405316730 / 1000000000000) (-12405278223 / 1000000000000)))) (orderedInterval (-3524476428 / 1000000000000) (-3524473162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (404510911186987 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (77915953790 / 1000000000000) (77915953792 / 1000000000000), orderedInterval (14589340523 / 1000000000000) (14589340525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1086573206614639 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37628226675 / 1000000000000) (37628312262 / 1000000000000), orderedInterval (-30527463491 / 1000000000000) (-30527377904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2950257624549363 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2211957904 / 1000000000000) (-2211957903 / 1000000000000), orderedInterval (-29294324619 / 1000000000000) (-29294324618 / 1000000000000)))) (orderedInterval (-810828288 / 1000000000000) (-810827153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2173146413230219 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18651934438 / 1000000000000) (-18651934437 / 1000000000000), orderedInterval (-28686477807 / 1000000000000) (-28686477806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3723723419164087 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25438485406 / 1000000000000) (25438543138 / 1000000000000), orderedInterval (-6074613616 / 1000000000000) (-6074555884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2742877816797733 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30401896730 / 1000000000000) (30401900147 / 1000000000000), orderedInterval (-2052233852 / 1000000000000) (-2052230435 / 1000000000000)))) (orderedInterval (1510370583 / 1000000000000) (1510377819 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks2_1 :
    compactCertificate599.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4208279933654059 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10069209359 / 1000000000000) (-10069209358 / 1000000000000), orderedInterval (-22438981830 / 1000000000000) (-22438981829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2429651552520211 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30929127899 / 1000000000000) (-30929104038 / 1000000000000), orderedInterval (9589627766 / 1000000000000) (9589651627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4311459316258799 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21477848131 / 1000000000000) (-21477848094 / 1000000000000), orderedInterval (-11362478974 / 1000000000000) (-11362478937 / 1000000000000)))) (orderedInterval (10884181402 / 1000000000000) (10884185210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4028324561041931 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13880035901 / 1000000000000) (13880035946 / 1000000000000), orderedInterval (-20970862929 / 1000000000000) (-20970862884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2874802485968123 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1818176754 / 1000000000000) (-1818176753 / 1000000000000), orderedInterval (-29705420500 / 1000000000000) (-29705420499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3259719619843917 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24895708920 / 1000000000000) (-24895660809 / 1000000000000), orderedInterval (12719600128 / 1000000000000) (12719648239 / 1000000000000)))) (orderedInterval (1178875125 / 1000000000000) (1178876011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2717614376171773 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30593207635 / 1000000000000) (30593209938 / 1000000000000), orderedInterval (-1063047033 / 1000000000000) (-1063044729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2401094718323233 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27658616242 / 1000000000000) (-27658616241 / 1000000000000), orderedInterval (-17168529017 / 1000000000000) (-17168529016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (695930836532067 / 800000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12435343887 / 1000000000000) (-12435343886 / 1000000000000), orderedInterval (-24017462425 / 1000000000000) (-24017462424 / 1000000000000)))) (orderedInterval (-2224798489 / 1000000000000) (-2224798336 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks2_2 :
    compactCertificate599.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1924981318681049 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35616899984 / 1000000000000) (-35616899956 / 1000000000000), orderedInterval (-7331502378 / 1000000000000) (-7331502350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1631827982430289 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12989028915 / 1000000000000) (12989028916 / 1000000000000), orderedInterval (37290823880 / 1000000000000) (37290823881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1021122183202267 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49921528037 / 1000000000000) (-49921527891 / 1000000000000), orderedInterval (1378699877 / 1000000000000) (1378700023 / 1000000000000)))) (orderedInterval (-4925520239 / 1000000000000) (-4925520129 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (549162906225189 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10503328895 / 1000000000000) (-10503328842 / 1000000000000), orderedInterval (67319220986 / 1000000000000) (67319221039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1491084117802567 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11953033059 / 1000000000000) (11953033129 / 1000000000000), orderedInterval (-39575229548 / 1000000000000) (-39575229478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2035947886157159 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26195697968 / 1000000000000) (26195697969 / 1000000000000), orderedInterval (23734398002 / 1000000000000) (23734398003 / 1000000000000)))) (orderedInterval (2506637963 / 1000000000000) (2506638015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (860877816797733 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37689681398 / 1000000000000) (37689718348 / 1000000000000), orderedInterval (-39298414911 / 1000000000000) (-39298377961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3499420530775493 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20512872399 / 1000000000000) (20512876022 / 1000000000000), orderedInterval (-17530512517 / 1000000000000) (-17530508894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2337450737190187 / 4000000000000) 2 (IntervalRat.scale (941 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23943321287 / 1000000000000) (23943321288 / 1000000000000), orderedInterval (22698296813 / 1000000000000) (22698296814 / 1000000000000)))) (orderedInterval (12661307592 / 1000000000000) (12661308930 / 1000000000000))) = true
  rfl'

theorem compactCertificate599_chunkChecks2 :
    compactCertificate599.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate599.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate599_chunkChecks2_0
    compactCertificate599_chunkChecks2_1 compactCertificate599_chunkChecks2_2

theorem compactCertificate599_chunkChecks3_0 :
    compactCertificate599.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (941 / 2) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1700086779 / 1000000000000) (1700086780 / 1000000000000), orderedInterval (36743004964 / 1000000000000) (36743004965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1386272681974841 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41942438061 / 1000000000000) (41942440485 / 1000000000000), orderedInterval (-8878399535 / 1000000000000) (-8878397111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (448292102580953 / 800000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31350925922 / 1000000000000) (31350964430 / 1000000000000), orderedInterval (-12405316730 / 1000000000000) (-12405278223 / 1000000000000)))) (orderedInterval (-13293210937 / 1000000000000) (-13293207054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (404510911186987 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (77915953790 / 1000000000000) (77915953792 / 1000000000000), orderedInterval (14589340523 / 1000000000000) (14589340525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1086573206614639 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37628226675 / 1000000000000) (37628312262 / 1000000000000), orderedInterval (-30527463491 / 1000000000000) (-30527377904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2950257624549363 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2211957904 / 1000000000000) (-2211957903 / 1000000000000), orderedInterval (-29294324619 / 1000000000000) (-29294324618 / 1000000000000)))) (orderedInterval (-7804706402 / 1000000000000) (-7804705665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2173146413230219 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18651934438 / 1000000000000) (-18651934437 / 1000000000000), orderedInterval (-28686477807 / 1000000000000) (-28686477806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3723723419164087 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25438485406 / 1000000000000) (25438543138 / 1000000000000), orderedInterval (-6074613616 / 1000000000000) (-6074555884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2742877816797733 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30401896730 / 1000000000000) (30401900147 / 1000000000000), orderedInterval (-2052233852 / 1000000000000) (-2052230435 / 1000000000000)))) (orderedInterval (-1300985241 / 1000000000000) (-1300971028 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate599_chunkChecks3_1 :
    compactCertificate599.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4208279933654059 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10069209359 / 1000000000000) (-10069209358 / 1000000000000), orderedInterval (-22438981830 / 1000000000000) (-22438981829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2429651552520211 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30929127899 / 1000000000000) (-30929104038 / 1000000000000), orderedInterval (9589627766 / 1000000000000) (9589651627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4311459316258799 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21477848131 / 1000000000000) (-21477848094 / 1000000000000), orderedInterval (-11362478974 / 1000000000000) (-11362478937 / 1000000000000)))) (orderedInterval (-26709304013 / 1000000000000) (-26709298322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4028324561041931 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13880035901 / 1000000000000) (13880035946 / 1000000000000), orderedInterval (-20970862929 / 1000000000000) (-20970862884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2874802485968123 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1818176754 / 1000000000000) (-1818176753 / 1000000000000), orderedInterval (-29705420500 / 1000000000000) (-29705420499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3259719619843917 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24895708920 / 1000000000000) (-24895660809 / 1000000000000), orderedInterval (12719600128 / 1000000000000) (12719648239 / 1000000000000)))) (orderedInterval (6631326982 / 1000000000000) (6631328512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2717614376171773 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30593207635 / 1000000000000) (30593209938 / 1000000000000), orderedInterval (-1063047033 / 1000000000000) (-1063044729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2401094718323233 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27658616242 / 1000000000000) (-27658616241 / 1000000000000), orderedInterval (-17168529017 / 1000000000000) (-17168529016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (695930836532067 / 800000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12435343887 / 1000000000000) (-12435343886 / 1000000000000), orderedInterval (-24017462425 / 1000000000000) (-24017462424 / 1000000000000)))) (orderedInterval (1888081581 / 1000000000000) (1888081810 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate599_chunkChecks3_2 :
    compactCertificate599.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1924981318681049 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35616899984 / 1000000000000) (-35616899956 / 1000000000000), orderedInterval (-7331502378 / 1000000000000) (-7331502350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1631827982430289 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12989028915 / 1000000000000) (12989028916 / 1000000000000), orderedInterval (37290823880 / 1000000000000) (37290823881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1021122183202267 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49921528037 / 1000000000000) (-49921527891 / 1000000000000), orderedInterval (1378699877 / 1000000000000) (1378700023 / 1000000000000)))) (orderedInterval (124766357 / 1000000000000) (124766464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (549162906225189 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10503328895 / 1000000000000) (-10503328842 / 1000000000000), orderedInterval (67319220986 / 1000000000000) (67319221039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1491084117802567 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11953033059 / 1000000000000) (11953033129 / 1000000000000), orderedInterval (-39575229548 / 1000000000000) (-39575229478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2035947886157159 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26195697968 / 1000000000000) (26195697969 / 1000000000000), orderedInterval (23734398002 / 1000000000000) (23734398003 / 1000000000000)))) (orderedInterval (1881889289 / 1000000000000) (1881889342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (860877816797733 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37689681398 / 1000000000000) (37689718348 / 1000000000000), orderedInterval (-39298414911 / 1000000000000) (-39298377961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3499420530775493 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20512872399 / 1000000000000) (20512876022 / 1000000000000), orderedInterval (-17530512517 / 1000000000000) (-17530508894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2337450737190187 / 4000000000000) 3 (IntervalRat.scale (941 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23943321287 / 1000000000000) (23943321288 / 1000000000000), orderedInterval (22698296813 / 1000000000000) (22698296814 / 1000000000000)))) (orderedInterval (-1018874715 / 1000000000000) (-1018872378 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate599_chunkChecks3 :
    compactCertificate599.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate599.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate599_chunkChecks3_0
    compactCertificate599_chunkChecks3_1 compactCertificate599_chunkChecks3_2

theorem compactCertificate599_chunkChecks4_0 :
    compactCertificate599.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (941 / 2) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1700086779 / 1000000000000) (1700086780 / 1000000000000), orderedInterval (36743004964 / 1000000000000) (36743004965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1386272681974841 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41942438061 / 1000000000000) (41942440485 / 1000000000000), orderedInterval (-8878399535 / 1000000000000) (-8878397111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (448292102580953 / 800000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31350925922 / 1000000000000) (31350964430 / 1000000000000), orderedInterval (-12405316730 / 1000000000000) (-12405278223 / 1000000000000)))) (orderedInterval (4547043196 / 1000000000000) (4547047823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (404510911186987 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (77915953790 / 1000000000000) (77915953792 / 1000000000000), orderedInterval (14589340523 / 1000000000000) (14589340525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1086573206614639 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37628226675 / 1000000000000) (37628312262 / 1000000000000), orderedInterval (-30527463491 / 1000000000000) (-30527377904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2950257624549363 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-2211957904 / 1000000000000) (-2211957903 / 1000000000000), orderedInterval (-29294324619 / 1000000000000) (-29294324618 / 1000000000000)))) (orderedInterval (1133628988 / 1000000000000) (1133629543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2173146413230219 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18651934438 / 1000000000000) (-18651934437 / 1000000000000), orderedInterval (-28686477807 / 1000000000000) (-28686477806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3723723419164087 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25438485406 / 1000000000000) (25438543138 / 1000000000000), orderedInterval (-6074613616 / 1000000000000) (-6074555884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2742877816797733 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30401896730 / 1000000000000) (30401900147 / 1000000000000), orderedInterval (-2052233852 / 1000000000000) (-2052230435 / 1000000000000)))) (orderedInterval (-8704670032 / 1000000000000) (-8704642034 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate599_chunkChecks4_1 :
    compactCertificate599.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4208279933654059 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10069209359 / 1000000000000) (-10069209358 / 1000000000000), orderedInterval (-22438981830 / 1000000000000) (-22438981829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2429651552520211 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30929127899 / 1000000000000) (-30929104038 / 1000000000000), orderedInterval (9589627766 / 1000000000000) (9589651627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4311459316258799 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21477848131 / 1000000000000) (-21477848094 / 1000000000000), orderedInterval (-11362478974 / 1000000000000) (-11362478937 / 1000000000000)))) (orderedInterval (-45618336049 / 1000000000000) (-45618326942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4028324561041931 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13880035901 / 1000000000000) (13880035946 / 1000000000000), orderedInterval (-20970862929 / 1000000000000) (-20970862884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2874802485968123 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1818176754 / 1000000000000) (-1818176753 / 1000000000000), orderedInterval (-29705420500 / 1000000000000) (-29705420499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3259719619843917 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24895708920 / 1000000000000) (-24895660809 / 1000000000000), orderedInterval (12719600128 / 1000000000000) (12719648239 / 1000000000000)))) (orderedInterval (-5090085040 / 1000000000000) (-5090082382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2717614376171773 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30593207635 / 1000000000000) (30593209938 / 1000000000000), orderedInterval (-1063047033 / 1000000000000) (-1063044729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2401094718323233 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27658616242 / 1000000000000) (-27658616241 / 1000000000000), orderedInterval (-17168529017 / 1000000000000) (-17168529016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (695930836532067 / 800000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12435343887 / 1000000000000) (-12435343886 / 1000000000000), orderedInterval (-24017462425 / 1000000000000) (-24017462424 / 1000000000000)))) (orderedInterval (2000822775 / 1000000000000) (2000823128 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate599_chunkChecks4_2 :
    compactCertificate599.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1924981318681049 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35616899984 / 1000000000000) (-35616899956 / 1000000000000), orderedInterval (-7331502378 / 1000000000000) (-7331502350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1631827982430289 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12989028915 / 1000000000000) (12989028916 / 1000000000000), orderedInterval (37290823880 / 1000000000000) (37290823881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1021122183202267 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49921528037 / 1000000000000) (-49921527891 / 1000000000000), orderedInterval (1378699877 / 1000000000000) (1378700023 / 1000000000000)))) (orderedInterval (5676271767 / 1000000000000) (5676271872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (549162906225189 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10503328895 / 1000000000000) (-10503328842 / 1000000000000), orderedInterval (67319220986 / 1000000000000) (67319221039 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1491084117802567 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (11953033059 / 1000000000000) (11953033129 / 1000000000000), orderedInterval (-39575229548 / 1000000000000) (-39575229478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2035947886157159 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26195697968 / 1000000000000) (26195697969 / 1000000000000), orderedInterval (23734398002 / 1000000000000) (23734398003 / 1000000000000)))) (orderedInterval (-2863019595 / 1000000000000) (-2863019539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (860877816797733 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37689681398 / 1000000000000) (37689718348 / 1000000000000), orderedInterval (-39298414911 / 1000000000000) (-39298377961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3499420530775493 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20512872399 / 1000000000000) (20512876022 / 1000000000000), orderedInterval (-17530512517 / 1000000000000) (-17530508894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2337450737190187 / 4000000000000) 4 (IntervalRat.scale (941 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23943321287 / 1000000000000) (23943321288 / 1000000000000), orderedInterval (22698296813 / 1000000000000) (22698296814 / 1000000000000)))) (orderedInterval (-30635750021 / 1000000000000) (-30635745808 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate599_chunkChecks4 :
    compactCertificate599.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate599.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate599_chunkChecks4_0
    compactCertificate599_chunkChecks4_1 compactCertificate599_chunkChecks4_2

theorem compactCertificate599_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate599.chunkCheck r b = true :=
  compactCertificate599.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate599_chunkChecks0
    · exact compactCertificate599_chunkChecks1
    · exact compactCertificate599_chunkChecks2
    · exact compactCertificate599_chunkChecks3
    · exact compactCertificate599_chunkChecks4)

theorem compactCertificate599_coefficient0 :
    compactCertificate599.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate599_coefficient1 :
    compactCertificate599.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate599_coefficient2 :
    compactCertificate599.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate599_coefficient3 :
    compactCertificate599.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate599_coefficient4 :
    compactCertificate599.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate599_coefficients : ∀ r : Fin 5,
    compactCertificate599.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate599_coefficient0
  · exact compactCertificate599_coefficient1
  · exact compactCertificate599_coefficient2
  · exact compactCertificate599_coefficient3
  · exact compactCertificate599_coefficient4

theorem compactCertificate599_lower : (1 : ℚ) ≤ compactCertificate599.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate599, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate599_proves {t : ℝ} (ht : t ∈ compactCertificate599.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate599.proves compactCertificate599_states compactCertificate599_chunks
    compactCertificate599_coefficients compactCertificate599_lower ht

end Erdos232
