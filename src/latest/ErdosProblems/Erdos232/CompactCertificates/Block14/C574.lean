/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate574 : CompactCertificate where
  left := 445
  right := 446
  center := 891 / 2
  grid := fun i =>
    match i.val with
    | 0 => 142
    | 1 => 105
    | 2 => 169
    | 3 => 30
    | 4 => 82
    | 5 => 222
    | 6 => 164
    | 7 => 281
    | 8 => 207
    | 9 => 317
    | 10 => 183
    | 11 => 325
    | 12 => 304
    | 13 => 217
    | 14 => 246
    | 15 => 205
    | 16 => 181
    | 17 => 262
    | 18 => 145
    | 19 => 123
    | 20 => 77
    | 21 => 41
    | 22 => 112
    | 23 => 153
    | 24 => 65
    | 25 => 264
    | _ => 176
  point := fun i =>
    match i.val with
    | 0 => 891 / 2
    | 1 => 1312613134579791 / 4000000000000
    | 2 => 424472118384303 / 800000000000
    | 3 => 383017238966637 / 4000000000000
    | 4 => 1028838179695689 / 4000000000000
    | 5 => 2793495795402213 / 4000000000000
    | 6 => 2057676359392269 / 4000000000000
    | 7 => 3525863513788737 / 4000000000000
    | 8 => 2597135106022083 / 4000000000000
    | 9 => 3984673135904109 / 4000000000000
    | 10 => 2300552107646661 / 4000000000000
    | 11 => 4082370085851849 / 4000000000000
    | 12 => 3814279685322381 / 4000000000000
    | 13 => 2722049962802973 / 4000000000000
    | 14 => 3086514539087067 / 4000000000000
    | 15 => 2573214037374123 / 4000000000000
    | 16 => 2273512639772583 / 4000000000000
    | 17 => 658952577417717 / 800000000000
    | 18 => 1822697507911599 / 4000000000000
    | 19 => 1545120863278839 / 4000000000000
    | 20 => 966864893977917 / 4000000000000
    | 21 => 519983155628739 / 4000000000000
    | 22 => 1411855418663217 / 4000000000000
    | 23 => 1927767870952209 / 4000000000000
    | 24 => 815135106022083 / 4000000000000
    | 25 => 3313478951031843 / 4000000000000
    | _ => 2213250379209837 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (6729042073 / 1000000000000) (6729042074 / 1000000000000), orderedInterval (37190854286 / 1000000000000) (37190854287 / 1000000000000))
    | 1 => (orderedInterval (35279438641 / 1000000000000) (35279531772 / 1000000000000), orderedInterval (-26423564540 / 1000000000000) (-26423471409 / 1000000000000))
    | 2 => (orderedInterval (-14946470555 / 1000000000000) (-14946470554 / 1000000000000), orderedInterval (-31233902956 / 1000000000000) (-31233902955 / 1000000000000))
    | 3 => (orderedInterval (61309705266 / 1000000000000) (61309804519 / 1000000000000), orderedInterval (-54074927499 / 1000000000000) (-54074828246 / 1000000000000))
    | 4 => (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))
    | 5 => (orderedInterval (29831241084 / 1000000000000) (29831250240 / 1000000000000), orderedInterval (-4676562877 / 1000000000000) (-4676553721 / 1000000000000))
    | 6 => (orderedInterval (-596258613 / 1000000000000) (-596258612 / 1000000000000), orderedInterval (35174375066 / 1000000000000) (35174375067 / 1000000000000))
    | 7 => (orderedInterval (13733997717 / 1000000000000) (13733997774 / 1000000000000), orderedInterval (-23107700709 / 1000000000000) (-23107700652 / 1000000000000))
    | 8 => (orderedInterval (7464350880 / 1000000000000) (7464350884 / 1000000000000), orderedInterval (-30415929800 / 1000000000000) (-30415929796 / 1000000000000))
    | 9 => (orderedInterval (-22159481438 / 1000000000000) (-22159481422 / 1000000000000), orderedInterval (-12155464722 / 1000000000000) (-12155464706 / 1000000000000))
    | 10 => (orderedInterval (-28205129988 / 1000000000000) (-28205129987 / 1000000000000), orderedInterval (-17621146974 / 1000000000000) (-17621146972 / 1000000000000))
    | 11 => (orderedInterval (-8802535948 / 1000000000000) (-8802535947 / 1000000000000), orderedInterval (-23368537087 / 1000000000000) (-23368537086 / 1000000000000))
    | 12 => (orderedInterval (-16426663112 / 1000000000000) (-16426662828 / 1000000000000), orderedInterval (19953087450 / 1000000000000) (19953087733 / 1000000000000))
    | 13 => (orderedInterval (12691995543 / 1000000000000) (12691995595 / 1000000000000), orderedInterval (-27837618673 / 1000000000000) (-27837618621 / 1000000000000))
    | 14 => (orderedInterval (-11657737537 / 1000000000000) (-11657737515 / 1000000000000), orderedInterval (26258861736 / 1000000000000) (26258861758 / 1000000000000))
    | 15 => (orderedInterval (-1956033531 / 1000000000000) (-1956033530 / 1000000000000), orderedInterval (-31395685295 / 1000000000000) (-31395685294 / 1000000000000))
    | 16 => (orderedInterval (-17064981359 / 1000000000000) (-17064981358 / 1000000000000), orderedInterval (-28774749525 / 1000000000000) (-28774749524 / 1000000000000))
    | 17 => (orderedInterval (27289439361 / 1000000000000) (27289439731 / 1000000000000), orderedInterval (5291283545 / 1000000000000) (5291283914 / 1000000000000))
    | 18 => (orderedInterval (-29930639997 / 1000000000000) (-29930639996 / 1000000000000), orderedInterval (-22355775287 / 1000000000000) (-22355775286 / 1000000000000))
    | 19 => (orderedInterval (-24548863417 / 1000000000000) (-24548863416 / 1000000000000), orderedInterval (-32301353825 / 1000000000000) (-32301353824 / 1000000000000))
    | 20 => (orderedInterval (-28912624599 / 1000000000000) (-28912624598 / 1000000000000), orderedInterval (-42340792658 / 1000000000000) (-42340792657 / 1000000000000))
    | 21 => (orderedInterval (-64342723590 / 1000000000000) (-64342717385 / 1000000000000), orderedInterval (27765159958 / 1000000000000) (27765166163 / 1000000000000))
    | 22 => (orderedInterval (40316994777 / 1000000000000) (40317003047 / 1000000000000), orderedInterval (-13405459140 / 1000000000000) (-13405450870 / 1000000000000))
    | 23 => (orderedInterval (-32023100365 / 1000000000000) (-32023024851 / 1000000000000), orderedInterval (17222423658 / 1000000000000) (17222499172 / 1000000000000))
    | 24 => (orderedInterval (-19952863217 / 1000000000000) (-19952863216 / 1000000000000), orderedInterval (-52161068251 / 1000000000000) (-52161068250 / 1000000000000))
    | 25 => (orderedInterval (-6197851913 / 1000000000000) (-6197851912 / 1000000000000), orderedInterval (27024252443 / 1000000000000) (27024252445 / 1000000000000))
    | _ => (orderedInterval (31329632962 / 1000000000000) (31329632965 / 1000000000000), orderedInterval (12972248643 / 1000000000000) (12972248646 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (2118816693 / 1000000000000) (2118817593 / 1000000000000)
      | 1 => orderedInterval (-2105588603 / 1000000000000) (-2105586822 / 1000000000000)
      | 2 => orderedInterval (-243212820 / 1000000000000) (-243212793 / 1000000000000)
      | 3 => orderedInterval (596371825 / 1000000000000) (596372005 / 1000000000000)
      | 4 => orderedInterval (1555738271 / 1000000000000) (1555738334 / 1000000000000)
      | 5 => orderedInterval (1652701966 / 1000000000000) (1652702018 / 1000000000000)
      | 6 => orderedInterval (5233889324 / 1000000000000) (5233889436 / 1000000000000)
      | 7 => orderedInterval (2727637932 / 1000000000000) (2727644075 / 1000000000000)
      | _ => orderedInterval (-5494036532 / 1000000000000) (-5494036408 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12376878604 / 1000000000000) (12376879279 / 1000000000000)
      | 1 => orderedInterval (1618917518 / 1000000000000) (1618918831 / 1000000000000)
      | 2 => orderedInterval (338870198 / 1000000000000) (338870245 / 1000000000000)
      | 3 => orderedInterval (-4466149811 / 1000000000000) (-4466149438 / 1000000000000)
      | 4 => orderedInterval (-5022249959 / 1000000000000) (-5022249854 / 1000000000000)
      | 5 => orderedInterval (1827840215 / 1000000000000) (1827840295 / 1000000000000)
      | 6 => orderedInterval (4493490987 / 1000000000000) (4493491091 / 1000000000000)
      | 7 => orderedInterval (-1336526421 / 1000000000000) (-1336519930 / 1000000000000)
      | _ => orderedInterval (-7257179066 / 1000000000000) (-7257178892 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1629188511 / 1000000000000) (-1629187998 / 1000000000000)
      | 1 => orderedInterval (5011784407 / 1000000000000) (5011786144 / 1000000000000)
      | 2 => orderedInterval (1274432724 / 1000000000000) (1274432809 / 1000000000000)
      | 3 => orderedInterval (-9627163279 / 1000000000000) (-9627162480 / 1000000000000)
      | 4 => orderedInterval (-4324817173 / 1000000000000) (-4324816995 / 1000000000000)
      | 5 => orderedInterval (-3935140225 / 1000000000000) (-3935140101 / 1000000000000)
      | 6 => orderedInterval (-5784381697 / 1000000000000) (-5784381598 / 1000000000000)
      | 7 => orderedInterval (-2396154563 / 1000000000000) (-2396147601 / 1000000000000)
      | _ => orderedInterval (7364790130 / 1000000000000) (7364790387 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11542616292 / 1000000000000) (-11542615897 / 1000000000000)
      | 1 => orderedInterval (-1621672803 / 1000000000000) (-1621670155 / 1000000000000)
      | 2 => orderedInterval (-3248007885 / 1000000000000) (-3248007730 / 1000000000000)
      | 3 => orderedInterval (18622782815 / 1000000000000) (18622784567 / 1000000000000)
      | 4 => orderedInterval (13615108343 / 1000000000000) (13615108653 / 1000000000000)
      | 5 => orderedInterval (-3175457173 / 1000000000000) (-3175456971 / 1000000000000)
      | 6 => orderedInterval (-4783679957 / 1000000000000) (-4783679861 / 1000000000000)
      | 7 => orderedInterval (1537887658 / 1000000000000) (1537895145 / 1000000000000)
      | _ => orderedInterval (18818868221 / 1000000000000) (18818868617 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (1050992501 / 1000000000000) (1050992814 / 1000000000000)
      | 1 => orderedInterval (-12725282408 / 1000000000000) (-12725278270 / 1000000000000)
      | 2 => orderedInterval (-5663798708 / 1000000000000) (-5663798420 / 1000000000000)
      | 3 => orderedInterval (58082203628 / 1000000000000) (58082207519 / 1000000000000)
      | 4 => orderedInterval (13228909336 / 1000000000000) (13228909891 / 1000000000000)
      | 5 => orderedInterval (10668636968 / 1000000000000) (10668637304 / 1000000000000)
      | 6 => orderedInterval (5963303105 / 1000000000000) (5963303200 / 1000000000000)
      | 7 => orderedInterval (3002531194 / 1000000000000) (3002539280 / 1000000000000)
      | _ => orderedInterval (-8046354095 / 1000000000000) (-8046353459 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (6042318056 / 1000000000000) (6042327438 / 1000000000000)
    | 1 => orderedInterval (2573892265 / 1000000000000) (2573901627 / 1000000000000)
    | 2 => orderedInterval (-14045838187 / 1000000000000) (-14045827433 / 1000000000000)
    | 3 => orderedInterval (28223212927 / 1000000000000) (28223226368 / 1000000000000)
    | _ => orderedInterval (65561141521 / 1000000000000) (65561159859 / 1000000000000)

theorem compactCertificate574_stateChecks0 :
    compactCertificate574.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (891 / 2)) (orderedInterval (6729042073 / 1000000000000) (6729042074 / 1000000000000), orderedInterval (37190854286 / 1000000000000) (37190854287 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1312613134579791 / 4000000000000)) (orderedInterval (35279438641 / 1000000000000) (35279531772 / 1000000000000), orderedInterval (-26423564540 / 1000000000000) (-26423471409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (424472118384303 / 800000000000)) (orderedInterval (-14946470555 / 1000000000000) (-14946470554 / 1000000000000), orderedInterval (-31233902956 / 1000000000000) (-31233902955 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_stateChecks1 :
    compactCertificate574.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (383017238966637 / 4000000000000)) (orderedInterval (61309705266 / 1000000000000) (61309804519 / 1000000000000), orderedInterval (-54074927499 / 1000000000000) (-54074828246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1028838179695689 / 4000000000000)) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2793495795402213 / 4000000000000)) (orderedInterval (29831241084 / 1000000000000) (29831250240 / 1000000000000), orderedInterval (-4676562877 / 1000000000000) (-4676553721 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_stateChecks2 :
    compactCertificate574.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2057676359392269 / 4000000000000)) (orderedInterval (-596258613 / 1000000000000) (-596258612 / 1000000000000), orderedInterval (35174375066 / 1000000000000) (35174375067 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (3525863513788737 / 4000000000000)) (orderedInterval (13733997717 / 1000000000000) (13733997774 / 1000000000000), orderedInterval (-23107700709 / 1000000000000) (-23107700652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2597135106022083 / 4000000000000)) (orderedInterval (7464350880 / 1000000000000) (7464350884 / 1000000000000), orderedInterval (-30415929800 / 1000000000000) (-30415929796 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_stateChecks3 :
    compactCertificate574.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 317 12 (3984673135904109 / 4000000000000)) (orderedInterval (-22159481438 / 1000000000000) (-22159481422 / 1000000000000), orderedInterval (-12155464722 / 1000000000000) (-12155464706 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2300552107646661 / 4000000000000)) (orderedInterval (-28205129988 / 1000000000000) (-28205129987 / 1000000000000), orderedInterval (-17621146974 / 1000000000000) (-17621146972 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 325 12 (4082370085851849 / 4000000000000)) (orderedInterval (-8802535948 / 1000000000000) (-8802535947 / 1000000000000), orderedInterval (-23368537087 / 1000000000000) (-23368537086 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_stateChecks4 :
    compactCertificate574.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 304 12 (3814279685322381 / 4000000000000)) (orderedInterval (-16426663112 / 1000000000000) (-16426662828 / 1000000000000), orderedInterval (19953087450 / 1000000000000) (19953087733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2722049962802973 / 4000000000000)) (orderedInterval (12691995543 / 1000000000000) (12691995595 / 1000000000000), orderedInterval (-27837618673 / 1000000000000) (-27837618621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3086514539087067 / 4000000000000)) (orderedInterval (-11657737537 / 1000000000000) (-11657737515 / 1000000000000), orderedInterval (26258861736 / 1000000000000) (26258861758 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_stateChecks5 :
    compactCertificate574.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2573214037374123 / 4000000000000)) (orderedInterval (-1956033531 / 1000000000000) (-1956033530 / 1000000000000), orderedInterval (-31395685295 / 1000000000000) (-31395685294 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2273512639772583 / 4000000000000)) (orderedInterval (-17064981359 / 1000000000000) (-17064981358 / 1000000000000), orderedInterval (-28774749525 / 1000000000000) (-28774749524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (658952577417717 / 800000000000)) (orderedInterval (27289439361 / 1000000000000) (27289439731 / 1000000000000), orderedInterval (5291283545 / 1000000000000) (5291283914 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_stateChecks6 :
    compactCertificate574.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1822697507911599 / 4000000000000)) (orderedInterval (-29930639997 / 1000000000000) (-29930639996 / 1000000000000), orderedInterval (-22355775287 / 1000000000000) (-22355775286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1545120863278839 / 4000000000000)) (orderedInterval (-24548863417 / 1000000000000) (-24548863416 / 1000000000000), orderedInterval (-32301353825 / 1000000000000) (-32301353824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (966864893977917 / 4000000000000)) (orderedInterval (-28912624599 / 1000000000000) (-28912624598 / 1000000000000), orderedInterval (-42340792658 / 1000000000000) (-42340792657 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_stateChecks7 :
    compactCertificate574.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (519983155628739 / 4000000000000)) (orderedInterval (-64342723590 / 1000000000000) (-64342717385 / 1000000000000), orderedInterval (27765159958 / 1000000000000) (27765166163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1411855418663217 / 4000000000000)) (orderedInterval (40316994777 / 1000000000000) (40317003047 / 1000000000000), orderedInterval (-13405459140 / 1000000000000) (-13405450870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1927767870952209 / 4000000000000)) (orderedInterval (-32023100365 / 1000000000000) (-32023024851 / 1000000000000), orderedInterval (17222423658 / 1000000000000) (17222499172 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_stateChecks8 :
    compactCertificate574.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (815135106022083 / 4000000000000)) (orderedInterval (-19952863217 / 1000000000000) (-19952863216 / 1000000000000), orderedInterval (-52161068251 / 1000000000000) (-52161068250 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (3313478951031843 / 4000000000000)) (orderedInterval (-6197851913 / 1000000000000) (-6197851912 / 1000000000000), orderedInterval (27024252443 / 1000000000000) (27024252445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2213250379209837 / 4000000000000)) (orderedInterval (31329632962 / 1000000000000) (31329632965 / 1000000000000), orderedInterval (12972248643 / 1000000000000) (12972248646 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_states : ∀ j,
    BesselStateValid (compactCertificate574.point j) (compactCertificate574.state j) :=
  compactCertificate574.statesValid_of_checks3 compactCertificate574_stateChecks0
    compactCertificate574_stateChecks1 compactCertificate574_stateChecks2
    compactCertificate574_stateChecks3 compactCertificate574_stateChecks4
    compactCertificate574_stateChecks5 compactCertificate574_stateChecks6
    compactCertificate574_stateChecks7 compactCertificate574_stateChecks8

theorem compactCertificate574_chunkChecks0_0 :
    compactCertificate574.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (891 / 2) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6729042073 / 1000000000000) (6729042074 / 1000000000000), orderedInterval (37190854286 / 1000000000000) (37190854287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1312613134579791 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35279438641 / 1000000000000) (35279531772 / 1000000000000), orderedInterval (-26423564540 / 1000000000000) (-26423471409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (424472118384303 / 800000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14946470555 / 1000000000000) (-14946470554 / 1000000000000), orderedInterval (-31233902956 / 1000000000000) (-31233902955 / 1000000000000)))) (orderedInterval (2118816693 / 1000000000000) (2118817593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (383017238966637 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61309705266 / 1000000000000) (61309804519 / 1000000000000), orderedInterval (-54074927499 / 1000000000000) (-54074828246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2793495795402213 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29831241084 / 1000000000000) (29831250240 / 1000000000000), orderedInterval (-4676562877 / 1000000000000) (-4676553721 / 1000000000000)))) (orderedInterval (-2105588603 / 1000000000000) (-2105586822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2057676359392269 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-596258613 / 1000000000000) (-596258612 / 1000000000000), orderedInterval (35174375066 / 1000000000000) (35174375067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3525863513788737 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13733997717 / 1000000000000) (13733997774 / 1000000000000), orderedInterval (-23107700709 / 1000000000000) (-23107700652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2597135106022083 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7464350880 / 1000000000000) (7464350884 / 1000000000000), orderedInterval (-30415929800 / 1000000000000) (-30415929796 / 1000000000000)))) (orderedInterval (-243212820 / 1000000000000) (-243212793 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks0_1 :
    compactCertificate574.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3984673135904109 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22159481438 / 1000000000000) (-22159481422 / 1000000000000), orderedInterval (-12155464722 / 1000000000000) (-12155464706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2300552107646661 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28205129988 / 1000000000000) (-28205129987 / 1000000000000), orderedInterval (-17621146974 / 1000000000000) (-17621146972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4082370085851849 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8802535948 / 1000000000000) (-8802535947 / 1000000000000), orderedInterval (-23368537087 / 1000000000000) (-23368537086 / 1000000000000)))) (orderedInterval (596371825 / 1000000000000) (596372005 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3814279685322381 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16426663112 / 1000000000000) (-16426662828 / 1000000000000), orderedInterval (19953087450 / 1000000000000) (19953087733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2722049962802973 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12691995543 / 1000000000000) (12691995595 / 1000000000000), orderedInterval (-27837618673 / 1000000000000) (-27837618621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3086514539087067 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11657737537 / 1000000000000) (-11657737515 / 1000000000000), orderedInterval (26258861736 / 1000000000000) (26258861758 / 1000000000000)))) (orderedInterval (1555738271 / 1000000000000) (1555738334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2573214037374123 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1956033531 / 1000000000000) (-1956033530 / 1000000000000), orderedInterval (-31395685295 / 1000000000000) (-31395685294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2273512639772583 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17064981359 / 1000000000000) (-17064981358 / 1000000000000), orderedInterval (-28774749525 / 1000000000000) (-28774749524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (658952577417717 / 800000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27289439361 / 1000000000000) (27289439731 / 1000000000000), orderedInterval (5291283545 / 1000000000000) (5291283914 / 1000000000000)))) (orderedInterval (1652701966 / 1000000000000) (1652702018 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks0_2 :
    compactCertificate574.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1822697507911599 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29930639997 / 1000000000000) (-29930639996 / 1000000000000), orderedInterval (-22355775287 / 1000000000000) (-22355775286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1545120863278839 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24548863417 / 1000000000000) (-24548863416 / 1000000000000), orderedInterval (-32301353825 / 1000000000000) (-32301353824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (966864893977917 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28912624599 / 1000000000000) (-28912624598 / 1000000000000), orderedInterval (-42340792658 / 1000000000000) (-42340792657 / 1000000000000)))) (orderedInterval (5233889324 / 1000000000000) (5233889436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (519983155628739 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64342723590 / 1000000000000) (-64342717385 / 1000000000000), orderedInterval (27765159958 / 1000000000000) (27765166163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1411855418663217 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40316994777 / 1000000000000) (40317003047 / 1000000000000), orderedInterval (-13405459140 / 1000000000000) (-13405450870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1927767870952209 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32023100365 / 1000000000000) (-32023024851 / 1000000000000), orderedInterval (17222423658 / 1000000000000) (17222499172 / 1000000000000)))) (orderedInterval (2727637932 / 1000000000000) (2727644075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (815135106022083 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19952863217 / 1000000000000) (-19952863216 / 1000000000000), orderedInterval (-52161068251 / 1000000000000) (-52161068250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3313478951031843 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6197851913 / 1000000000000) (-6197851912 / 1000000000000), orderedInterval (27024252443 / 1000000000000) (27024252445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2213250379209837 / 4000000000000) 0 (IntervalRat.scale (891 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31329632962 / 1000000000000) (31329632965 / 1000000000000), orderedInterval (12972248643 / 1000000000000) (12972248646 / 1000000000000)))) (orderedInterval (-5494036532 / 1000000000000) (-5494036408 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks0 :
    compactCertificate574.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate574.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate574_chunkChecks0_0
    compactCertificate574_chunkChecks0_1 compactCertificate574_chunkChecks0_2

theorem compactCertificate574_chunkChecks1_0 :
    compactCertificate574.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (891 / 2) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6729042073 / 1000000000000) (6729042074 / 1000000000000), orderedInterval (37190854286 / 1000000000000) (37190854287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1312613134579791 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35279438641 / 1000000000000) (35279531772 / 1000000000000), orderedInterval (-26423564540 / 1000000000000) (-26423471409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (424472118384303 / 800000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14946470555 / 1000000000000) (-14946470554 / 1000000000000), orderedInterval (-31233902956 / 1000000000000) (-31233902955 / 1000000000000)))) (orderedInterval (12376878604 / 1000000000000) (12376879279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (383017238966637 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61309705266 / 1000000000000) (61309804519 / 1000000000000), orderedInterval (-54074927499 / 1000000000000) (-54074828246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2793495795402213 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29831241084 / 1000000000000) (29831250240 / 1000000000000), orderedInterval (-4676562877 / 1000000000000) (-4676553721 / 1000000000000)))) (orderedInterval (1618917518 / 1000000000000) (1618918831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2057676359392269 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-596258613 / 1000000000000) (-596258612 / 1000000000000), orderedInterval (35174375066 / 1000000000000) (35174375067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3525863513788737 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13733997717 / 1000000000000) (13733997774 / 1000000000000), orderedInterval (-23107700709 / 1000000000000) (-23107700652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2597135106022083 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7464350880 / 1000000000000) (7464350884 / 1000000000000), orderedInterval (-30415929800 / 1000000000000) (-30415929796 / 1000000000000)))) (orderedInterval (338870198 / 1000000000000) (338870245 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks1_1 :
    compactCertificate574.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3984673135904109 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22159481438 / 1000000000000) (-22159481422 / 1000000000000), orderedInterval (-12155464722 / 1000000000000) (-12155464706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2300552107646661 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28205129988 / 1000000000000) (-28205129987 / 1000000000000), orderedInterval (-17621146974 / 1000000000000) (-17621146972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4082370085851849 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8802535948 / 1000000000000) (-8802535947 / 1000000000000), orderedInterval (-23368537087 / 1000000000000) (-23368537086 / 1000000000000)))) (orderedInterval (-4466149811 / 1000000000000) (-4466149438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3814279685322381 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16426663112 / 1000000000000) (-16426662828 / 1000000000000), orderedInterval (19953087450 / 1000000000000) (19953087733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2722049962802973 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12691995543 / 1000000000000) (12691995595 / 1000000000000), orderedInterval (-27837618673 / 1000000000000) (-27837618621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3086514539087067 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11657737537 / 1000000000000) (-11657737515 / 1000000000000), orderedInterval (26258861736 / 1000000000000) (26258861758 / 1000000000000)))) (orderedInterval (-5022249959 / 1000000000000) (-5022249854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2573214037374123 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1956033531 / 1000000000000) (-1956033530 / 1000000000000), orderedInterval (-31395685295 / 1000000000000) (-31395685294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2273512639772583 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17064981359 / 1000000000000) (-17064981358 / 1000000000000), orderedInterval (-28774749525 / 1000000000000) (-28774749524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (658952577417717 / 800000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27289439361 / 1000000000000) (27289439731 / 1000000000000), orderedInterval (5291283545 / 1000000000000) (5291283914 / 1000000000000)))) (orderedInterval (1827840215 / 1000000000000) (1827840295 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks1_2 :
    compactCertificate574.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1822697507911599 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29930639997 / 1000000000000) (-29930639996 / 1000000000000), orderedInterval (-22355775287 / 1000000000000) (-22355775286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1545120863278839 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24548863417 / 1000000000000) (-24548863416 / 1000000000000), orderedInterval (-32301353825 / 1000000000000) (-32301353824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (966864893977917 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28912624599 / 1000000000000) (-28912624598 / 1000000000000), orderedInterval (-42340792658 / 1000000000000) (-42340792657 / 1000000000000)))) (orderedInterval (4493490987 / 1000000000000) (4493491091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (519983155628739 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64342723590 / 1000000000000) (-64342717385 / 1000000000000), orderedInterval (27765159958 / 1000000000000) (27765166163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1411855418663217 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40316994777 / 1000000000000) (40317003047 / 1000000000000), orderedInterval (-13405459140 / 1000000000000) (-13405450870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1927767870952209 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32023100365 / 1000000000000) (-32023024851 / 1000000000000), orderedInterval (17222423658 / 1000000000000) (17222499172 / 1000000000000)))) (orderedInterval (-1336526421 / 1000000000000) (-1336519930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (815135106022083 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19952863217 / 1000000000000) (-19952863216 / 1000000000000), orderedInterval (-52161068251 / 1000000000000) (-52161068250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3313478951031843 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6197851913 / 1000000000000) (-6197851912 / 1000000000000), orderedInterval (27024252443 / 1000000000000) (27024252445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2213250379209837 / 4000000000000) 1 (IntervalRat.scale (891 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31329632962 / 1000000000000) (31329632965 / 1000000000000), orderedInterval (12972248643 / 1000000000000) (12972248646 / 1000000000000)))) (orderedInterval (-7257179066 / 1000000000000) (-7257178892 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks1 :
    compactCertificate574.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate574.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate574_chunkChecks1_0
    compactCertificate574_chunkChecks1_1 compactCertificate574_chunkChecks1_2

theorem compactCertificate574_chunkChecks2_0 :
    compactCertificate574.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (891 / 2) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6729042073 / 1000000000000) (6729042074 / 1000000000000), orderedInterval (37190854286 / 1000000000000) (37190854287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1312613134579791 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35279438641 / 1000000000000) (35279531772 / 1000000000000), orderedInterval (-26423564540 / 1000000000000) (-26423471409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (424472118384303 / 800000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14946470555 / 1000000000000) (-14946470554 / 1000000000000), orderedInterval (-31233902956 / 1000000000000) (-31233902955 / 1000000000000)))) (orderedInterval (-1629188511 / 1000000000000) (-1629187998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (383017238966637 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61309705266 / 1000000000000) (61309804519 / 1000000000000), orderedInterval (-54074927499 / 1000000000000) (-54074828246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2793495795402213 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29831241084 / 1000000000000) (29831250240 / 1000000000000), orderedInterval (-4676562877 / 1000000000000) (-4676553721 / 1000000000000)))) (orderedInterval (5011784407 / 1000000000000) (5011786144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2057676359392269 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-596258613 / 1000000000000) (-596258612 / 1000000000000), orderedInterval (35174375066 / 1000000000000) (35174375067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3525863513788737 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13733997717 / 1000000000000) (13733997774 / 1000000000000), orderedInterval (-23107700709 / 1000000000000) (-23107700652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2597135106022083 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7464350880 / 1000000000000) (7464350884 / 1000000000000), orderedInterval (-30415929800 / 1000000000000) (-30415929796 / 1000000000000)))) (orderedInterval (1274432724 / 1000000000000) (1274432809 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks2_1 :
    compactCertificate574.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3984673135904109 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22159481438 / 1000000000000) (-22159481422 / 1000000000000), orderedInterval (-12155464722 / 1000000000000) (-12155464706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2300552107646661 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28205129988 / 1000000000000) (-28205129987 / 1000000000000), orderedInterval (-17621146974 / 1000000000000) (-17621146972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4082370085851849 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8802535948 / 1000000000000) (-8802535947 / 1000000000000), orderedInterval (-23368537087 / 1000000000000) (-23368537086 / 1000000000000)))) (orderedInterval (-9627163279 / 1000000000000) (-9627162480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3814279685322381 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16426663112 / 1000000000000) (-16426662828 / 1000000000000), orderedInterval (19953087450 / 1000000000000) (19953087733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2722049962802973 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12691995543 / 1000000000000) (12691995595 / 1000000000000), orderedInterval (-27837618673 / 1000000000000) (-27837618621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3086514539087067 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11657737537 / 1000000000000) (-11657737515 / 1000000000000), orderedInterval (26258861736 / 1000000000000) (26258861758 / 1000000000000)))) (orderedInterval (-4324817173 / 1000000000000) (-4324816995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2573214037374123 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1956033531 / 1000000000000) (-1956033530 / 1000000000000), orderedInterval (-31395685295 / 1000000000000) (-31395685294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2273512639772583 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17064981359 / 1000000000000) (-17064981358 / 1000000000000), orderedInterval (-28774749525 / 1000000000000) (-28774749524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (658952577417717 / 800000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27289439361 / 1000000000000) (27289439731 / 1000000000000), orderedInterval (5291283545 / 1000000000000) (5291283914 / 1000000000000)))) (orderedInterval (-3935140225 / 1000000000000) (-3935140101 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks2_2 :
    compactCertificate574.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1822697507911599 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29930639997 / 1000000000000) (-29930639996 / 1000000000000), orderedInterval (-22355775287 / 1000000000000) (-22355775286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1545120863278839 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24548863417 / 1000000000000) (-24548863416 / 1000000000000), orderedInterval (-32301353825 / 1000000000000) (-32301353824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (966864893977917 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28912624599 / 1000000000000) (-28912624598 / 1000000000000), orderedInterval (-42340792658 / 1000000000000) (-42340792657 / 1000000000000)))) (orderedInterval (-5784381697 / 1000000000000) (-5784381598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (519983155628739 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64342723590 / 1000000000000) (-64342717385 / 1000000000000), orderedInterval (27765159958 / 1000000000000) (27765166163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1411855418663217 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40316994777 / 1000000000000) (40317003047 / 1000000000000), orderedInterval (-13405459140 / 1000000000000) (-13405450870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1927767870952209 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32023100365 / 1000000000000) (-32023024851 / 1000000000000), orderedInterval (17222423658 / 1000000000000) (17222499172 / 1000000000000)))) (orderedInterval (-2396154563 / 1000000000000) (-2396147601 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (815135106022083 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19952863217 / 1000000000000) (-19952863216 / 1000000000000), orderedInterval (-52161068251 / 1000000000000) (-52161068250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3313478951031843 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6197851913 / 1000000000000) (-6197851912 / 1000000000000), orderedInterval (27024252443 / 1000000000000) (27024252445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2213250379209837 / 4000000000000) 2 (IntervalRat.scale (891 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31329632962 / 1000000000000) (31329632965 / 1000000000000), orderedInterval (12972248643 / 1000000000000) (12972248646 / 1000000000000)))) (orderedInterval (7364790130 / 1000000000000) (7364790387 / 1000000000000))) = true
  rfl'

theorem compactCertificate574_chunkChecks2 :
    compactCertificate574.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate574.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate574_chunkChecks2_0
    compactCertificate574_chunkChecks2_1 compactCertificate574_chunkChecks2_2

theorem compactCertificate574_chunkChecks3_0 :
    compactCertificate574.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (891 / 2) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6729042073 / 1000000000000) (6729042074 / 1000000000000), orderedInterval (37190854286 / 1000000000000) (37190854287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1312613134579791 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35279438641 / 1000000000000) (35279531772 / 1000000000000), orderedInterval (-26423564540 / 1000000000000) (-26423471409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (424472118384303 / 800000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14946470555 / 1000000000000) (-14946470554 / 1000000000000), orderedInterval (-31233902956 / 1000000000000) (-31233902955 / 1000000000000)))) (orderedInterval (-11542616292 / 1000000000000) (-11542615897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (383017238966637 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61309705266 / 1000000000000) (61309804519 / 1000000000000), orderedInterval (-54074927499 / 1000000000000) (-54074828246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2793495795402213 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29831241084 / 1000000000000) (29831250240 / 1000000000000), orderedInterval (-4676562877 / 1000000000000) (-4676553721 / 1000000000000)))) (orderedInterval (-1621672803 / 1000000000000) (-1621670155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2057676359392269 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-596258613 / 1000000000000) (-596258612 / 1000000000000), orderedInterval (35174375066 / 1000000000000) (35174375067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3525863513788737 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13733997717 / 1000000000000) (13733997774 / 1000000000000), orderedInterval (-23107700709 / 1000000000000) (-23107700652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2597135106022083 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7464350880 / 1000000000000) (7464350884 / 1000000000000), orderedInterval (-30415929800 / 1000000000000) (-30415929796 / 1000000000000)))) (orderedInterval (-3248007885 / 1000000000000) (-3248007730 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate574_chunkChecks3_1 :
    compactCertificate574.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3984673135904109 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22159481438 / 1000000000000) (-22159481422 / 1000000000000), orderedInterval (-12155464722 / 1000000000000) (-12155464706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2300552107646661 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28205129988 / 1000000000000) (-28205129987 / 1000000000000), orderedInterval (-17621146974 / 1000000000000) (-17621146972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4082370085851849 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8802535948 / 1000000000000) (-8802535947 / 1000000000000), orderedInterval (-23368537087 / 1000000000000) (-23368537086 / 1000000000000)))) (orderedInterval (18622782815 / 1000000000000) (18622784567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3814279685322381 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16426663112 / 1000000000000) (-16426662828 / 1000000000000), orderedInterval (19953087450 / 1000000000000) (19953087733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2722049962802973 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12691995543 / 1000000000000) (12691995595 / 1000000000000), orderedInterval (-27837618673 / 1000000000000) (-27837618621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3086514539087067 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11657737537 / 1000000000000) (-11657737515 / 1000000000000), orderedInterval (26258861736 / 1000000000000) (26258861758 / 1000000000000)))) (orderedInterval (13615108343 / 1000000000000) (13615108653 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2573214037374123 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1956033531 / 1000000000000) (-1956033530 / 1000000000000), orderedInterval (-31395685295 / 1000000000000) (-31395685294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2273512639772583 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17064981359 / 1000000000000) (-17064981358 / 1000000000000), orderedInterval (-28774749525 / 1000000000000) (-28774749524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (658952577417717 / 800000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27289439361 / 1000000000000) (27289439731 / 1000000000000), orderedInterval (5291283545 / 1000000000000) (5291283914 / 1000000000000)))) (orderedInterval (-3175457173 / 1000000000000) (-3175456971 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate574_chunkChecks3_2 :
    compactCertificate574.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1822697507911599 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29930639997 / 1000000000000) (-29930639996 / 1000000000000), orderedInterval (-22355775287 / 1000000000000) (-22355775286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1545120863278839 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24548863417 / 1000000000000) (-24548863416 / 1000000000000), orderedInterval (-32301353825 / 1000000000000) (-32301353824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (966864893977917 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28912624599 / 1000000000000) (-28912624598 / 1000000000000), orderedInterval (-42340792658 / 1000000000000) (-42340792657 / 1000000000000)))) (orderedInterval (-4783679957 / 1000000000000) (-4783679861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (519983155628739 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64342723590 / 1000000000000) (-64342717385 / 1000000000000), orderedInterval (27765159958 / 1000000000000) (27765166163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1411855418663217 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40316994777 / 1000000000000) (40317003047 / 1000000000000), orderedInterval (-13405459140 / 1000000000000) (-13405450870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1927767870952209 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32023100365 / 1000000000000) (-32023024851 / 1000000000000), orderedInterval (17222423658 / 1000000000000) (17222499172 / 1000000000000)))) (orderedInterval (1537887658 / 1000000000000) (1537895145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (815135106022083 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19952863217 / 1000000000000) (-19952863216 / 1000000000000), orderedInterval (-52161068251 / 1000000000000) (-52161068250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3313478951031843 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6197851913 / 1000000000000) (-6197851912 / 1000000000000), orderedInterval (27024252443 / 1000000000000) (27024252445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2213250379209837 / 4000000000000) 3 (IntervalRat.scale (891 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31329632962 / 1000000000000) (31329632965 / 1000000000000), orderedInterval (12972248643 / 1000000000000) (12972248646 / 1000000000000)))) (orderedInterval (18818868221 / 1000000000000) (18818868617 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate574_chunkChecks3 :
    compactCertificate574.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate574.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate574_chunkChecks3_0
    compactCertificate574_chunkChecks3_1 compactCertificate574_chunkChecks3_2

theorem compactCertificate574_chunkChecks4_0 :
    compactCertificate574.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (891 / 2) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6729042073 / 1000000000000) (6729042074 / 1000000000000), orderedInterval (37190854286 / 1000000000000) (37190854287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1312613134579791 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35279438641 / 1000000000000) (35279531772 / 1000000000000), orderedInterval (-26423564540 / 1000000000000) (-26423471409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (424472118384303 / 800000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14946470555 / 1000000000000) (-14946470554 / 1000000000000), orderedInterval (-31233902956 / 1000000000000) (-31233902955 / 1000000000000)))) (orderedInterval (1050992501 / 1000000000000) (1050992814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (383017238966637 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (61309705266 / 1000000000000) (61309804519 / 1000000000000), orderedInterval (-54074927499 / 1000000000000) (-54074828246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2793495795402213 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29831241084 / 1000000000000) (29831250240 / 1000000000000), orderedInterval (-4676562877 / 1000000000000) (-4676553721 / 1000000000000)))) (orderedInterval (-12725282408 / 1000000000000) (-12725278270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2057676359392269 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-596258613 / 1000000000000) (-596258612 / 1000000000000), orderedInterval (35174375066 / 1000000000000) (35174375067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3525863513788737 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13733997717 / 1000000000000) (13733997774 / 1000000000000), orderedInterval (-23107700709 / 1000000000000) (-23107700652 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2597135106022083 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7464350880 / 1000000000000) (7464350884 / 1000000000000), orderedInterval (-30415929800 / 1000000000000) (-30415929796 / 1000000000000)))) (orderedInterval (-5663798708 / 1000000000000) (-5663798420 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate574_chunkChecks4_1 :
    compactCertificate574.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3984673135904109 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22159481438 / 1000000000000) (-22159481422 / 1000000000000), orderedInterval (-12155464722 / 1000000000000) (-12155464706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2300552107646661 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28205129988 / 1000000000000) (-28205129987 / 1000000000000), orderedInterval (-17621146974 / 1000000000000) (-17621146972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4082370085851849 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8802535948 / 1000000000000) (-8802535947 / 1000000000000), orderedInterval (-23368537087 / 1000000000000) (-23368537086 / 1000000000000)))) (orderedInterval (58082203628 / 1000000000000) (58082207519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3814279685322381 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16426663112 / 1000000000000) (-16426662828 / 1000000000000), orderedInterval (19953087450 / 1000000000000) (19953087733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2722049962802973 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12691995543 / 1000000000000) (12691995595 / 1000000000000), orderedInterval (-27837618673 / 1000000000000) (-27837618621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3086514539087067 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11657737537 / 1000000000000) (-11657737515 / 1000000000000), orderedInterval (26258861736 / 1000000000000) (26258861758 / 1000000000000)))) (orderedInterval (13228909336 / 1000000000000) (13228909891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2573214037374123 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1956033531 / 1000000000000) (-1956033530 / 1000000000000), orderedInterval (-31395685295 / 1000000000000) (-31395685294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2273512639772583 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17064981359 / 1000000000000) (-17064981358 / 1000000000000), orderedInterval (-28774749525 / 1000000000000) (-28774749524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (658952577417717 / 800000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27289439361 / 1000000000000) (27289439731 / 1000000000000), orderedInterval (5291283545 / 1000000000000) (5291283914 / 1000000000000)))) (orderedInterval (10668636968 / 1000000000000) (10668637304 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate574_chunkChecks4_2 :
    compactCertificate574.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1822697507911599 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29930639997 / 1000000000000) (-29930639996 / 1000000000000), orderedInterval (-22355775287 / 1000000000000) (-22355775286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1545120863278839 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24548863417 / 1000000000000) (-24548863416 / 1000000000000), orderedInterval (-32301353825 / 1000000000000) (-32301353824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (966864893977917 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28912624599 / 1000000000000) (-28912624598 / 1000000000000), orderedInterval (-42340792658 / 1000000000000) (-42340792657 / 1000000000000)))) (orderedInterval (5963303105 / 1000000000000) (5963303200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (519983155628739 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64342723590 / 1000000000000) (-64342717385 / 1000000000000), orderedInterval (27765159958 / 1000000000000) (27765166163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1411855418663217 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40316994777 / 1000000000000) (40317003047 / 1000000000000), orderedInterval (-13405459140 / 1000000000000) (-13405450870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1927767870952209 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32023100365 / 1000000000000) (-32023024851 / 1000000000000), orderedInterval (17222423658 / 1000000000000) (17222499172 / 1000000000000)))) (orderedInterval (3002531194 / 1000000000000) (3002539280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (815135106022083 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19952863217 / 1000000000000) (-19952863216 / 1000000000000), orderedInterval (-52161068251 / 1000000000000) (-52161068250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3313478951031843 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6197851913 / 1000000000000) (-6197851912 / 1000000000000), orderedInterval (27024252443 / 1000000000000) (27024252445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2213250379209837 / 4000000000000) 4 (IntervalRat.scale (891 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31329632962 / 1000000000000) (31329632965 / 1000000000000), orderedInterval (12972248643 / 1000000000000) (12972248646 / 1000000000000)))) (orderedInterval (-8046354095 / 1000000000000) (-8046353459 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate574_chunkChecks4 :
    compactCertificate574.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate574.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate574_chunkChecks4_0
    compactCertificate574_chunkChecks4_1 compactCertificate574_chunkChecks4_2

theorem compactCertificate574_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate574.chunkCheck r b = true :=
  compactCertificate574.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate574_chunkChecks0
    · exact compactCertificate574_chunkChecks1
    · exact compactCertificate574_chunkChecks2
    · exact compactCertificate574_chunkChecks3
    · exact compactCertificate574_chunkChecks4)

theorem compactCertificate574_coefficient0 :
    compactCertificate574.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate574_coefficient1 :
    compactCertificate574.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate574_coefficient2 :
    compactCertificate574.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate574_coefficient3 :
    compactCertificate574.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate574_coefficient4 :
    compactCertificate574.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate574_coefficients : ∀ r : Fin 5,
    compactCertificate574.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate574_coefficient0
  · exact compactCertificate574_coefficient1
  · exact compactCertificate574_coefficient2
  · exact compactCertificate574_coefficient3
  · exact compactCertificate574_coefficient4

theorem compactCertificate574_lower : (1 : ℚ) ≤ compactCertificate574.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate574, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate574_proves {t : ℝ} (ht : t ∈ compactCertificate574.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate574.proves compactCertificate574_states compactCertificate574_chunks
    compactCertificate574_coefficients compactCertificate574_lower ht

end Erdos232
