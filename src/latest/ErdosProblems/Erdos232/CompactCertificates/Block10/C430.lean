/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate430 : CompactCertificate where
  left := 301
  right := 302
  center := 603 / 2
  grid := fun i =>
    match i.val with
    | 0 => 96
    | 1 => 71
    | 2 => 114
    | 3 => 21
    | 4 => 55
    | 5 => 151
    | 6 => 111
    | 7 => 190
    | 8 => 140
    | 9 => 215
    | 10 => 124
    | 11 => 220
    | 12 => 206
    | 13 => 147
    | 14 => 166
    | 15 => 139
    | 16 => 123
    | 17 => 178
    | 18 => 98
    | 19 => 83
    | 20 => 52
    | 21 => 28
    | 22 => 76
    | 23 => 104
    | 24 => 44
    | 25 => 179
    | _ => 119
  point := fun i =>
    match i.val with
    | 0 => 603 / 2
    | 1 => 888334141584303 / 4000000000000
    | 2 => 287269009411599 / 800000000000
    | 3 => 259213686977421 / 4000000000000
    | 4 => 696284424642537 / 4000000000000
    | 5 => 1890547659514629 / 4000000000000
    | 6 => 1392568849285677 / 4000000000000
    | 7 => 2386190458826721 / 4000000000000
    | 8 => 1757657091954339 / 4000000000000
    | 9 => 2696697980864397 / 4000000000000
    | 10 => 1556939305175013 / 4000000000000
    | 11 => 2762816118707817 / 4000000000000
    | 12 => 2581381201177773 / 4000000000000
    | 13 => 1842195429371709 / 4000000000000
    | 14 => 2088853273927611 / 4000000000000
    | 15 => 1741468085899659 / 4000000000000
    | 16 => 1538639867320839 / 4000000000000
    | 17 => 445957804919061 / 800000000000
    | 18 => 1233542757879567 / 4000000000000
    | 19 => 1045687856966487 / 4000000000000
    | 20 => 654342908045661 / 4000000000000
    | 21 => 351907792193187 / 4000000000000
    | 22 => 955498111620561 / 4000000000000
    | 23 => 1304650983371697 / 4000000000000
    | 24 => 551657091954339 / 4000000000000
    | 25 => 2242455451708419 / 4000000000000
    | _ => 1497856317243021 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (29323560058 / 1000000000000) (29323560059 / 1000000000000), orderedInterval (35329863162 / 1000000000000) (35329863163 / 1000000000000))
    | 1 => (orderedInterval (9833180864 / 1000000000000) (9833180908 / 1000000000000), orderedInterval (-52651914259 / 1000000000000) (-52651914215 / 1000000000000))
    | 2 => (orderedInterval (41574854122 / 1000000000000) (41574855629 / 1000000000000), orderedInterval (-6722569019 / 1000000000000) (-6722567512 / 1000000000000))
    | 3 => (orderedInterval (37365883670 / 1000000000000) (37365885367 / 1000000000000), orderedInterval (-92091664140 / 1000000000000) (-92091662442 / 1000000000000))
    | 4 => (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))
    | 5 => (orderedInterval (30032165857 / 1000000000000) (30032230058 / 1000000000000), orderedInterval (-21127297185 / 1000000000000) (-21127232984 / 1000000000000))
    | 6 => (orderedInterval (-8933759475 / 1000000000000) (-8933759474 / 1000000000000), orderedInterval (-41805939695 / 1000000000000) (-41805939694 / 1000000000000))
    | 7 => (orderedInterval (13624088091 / 1000000000000) (13624088092 / 1000000000000), orderedInterval (29679621832 / 1000000000000) (29679621833 / 1000000000000))
    | 8 => (orderedInterval (13991534438 / 1000000000000) (13991534439 / 1000000000000), orderedInterval (35382234616 / 1000000000000) (35382234617 / 1000000000000))
    | 9 => (orderedInterval (14264072419 / 1000000000000) (14264072538 / 1000000000000), orderedInterval (-27228801403 / 1000000000000) (-27228801284 / 1000000000000))
    | 10 => (orderedInterval (18041644282 / 1000000000000) (18041644283 / 1000000000000), orderedInterval (36171675150 / 1000000000000) (36171675151 / 1000000000000))
    | 11 => (orderedInterval (10091940239 / 1000000000000) (10091940240 / 1000000000000), orderedInterval (28625714625 / 1000000000000) (28625714626 / 1000000000000))
    | 12 => (orderedInterval (-27048121746 / 1000000000000) (-27048062049 / 1000000000000), orderedInterval (15985882179 / 1000000000000) (15985941877 / 1000000000000))
    | 13 => (orderedInterval (17173145031 / 1000000000000) (17173145510 / 1000000000000), orderedInterval (-32994245272 / 1000000000000) (-32994244792 / 1000000000000))
    | 14 => (orderedInterval (34812667011 / 1000000000000) (34812667238 / 1000000000000), orderedInterval (2642033237 / 1000000000000) (2642033464 / 1000000000000))
    | 15 => (orderedInterval (19306467646 / 1000000000000) (19306468668 / 1000000000000), orderedInterval (-33030062163 / 1000000000000) (-33030061142 / 1000000000000))
    | 16 => (orderedInterval (33577557972 / 1000000000000) (33577662083 / 1000000000000), orderedInterval (-23012437367 / 1000000000000) (-23012333257 / 1000000000000))
    | 17 => (orderedInterval (-27896391695 / 1000000000000) (-27896342444 / 1000000000000), orderedInterval (19099047362 / 1000000000000) (19099096613 / 1000000000000))
    | 18 => (orderedInterval (43713240379 / 1000000000000) (43713240382 / 1000000000000), orderedInterval (12319143826 / 1000000000000) (12319143828 / 1000000000000))
    | 19 => (orderedInterval (-49015669342 / 1000000000000) (-49015669323 / 1000000000000), orderedInterval (-5622804523 / 1000000000000) (-5622804504 / 1000000000000))
    | 20 => (orderedInterval (52746243755 / 1000000000000) (52746243756 / 1000000000000), orderedInterval (33147705963 / 1000000000000) (33147705964 / 1000000000000))
    | 21 => (orderedInterval (60804220168 / 1000000000000) (60804220169 / 1000000000000), orderedInterval (59144402653 / 1000000000000) (59144402654 / 1000000000000))
    | 22 => (orderedInterval (40386102402 / 1000000000000) (40386102403 / 1000000000000), orderedInterval (32071983703 / 1000000000000) (32071983704 / 1000000000000))
    | 23 => (orderedInterval (9732904496 / 1000000000000) (9732904497 / 1000000000000), orderedInterval (43079390554 / 1000000000000) (43079390555 / 1000000000000))
    | 24 => (orderedInterval (30690198943 / 1000000000000) (30690198944 / 1000000000000), orderedInterval (60503783111 / 1000000000000) (60503783112 / 1000000000000))
    | 25 => (orderedInterval (27333001723 / 1000000000000) (27333040581 / 1000000000000), orderedInterval (-19734343672 / 1000000000000) (-19734304813 / 1000000000000))
    | _ => (orderedInterval (-40629418422 / 1000000000000) (-40629418402 / 1000000000000), orderedInterval (-6969373232 / 1000000000000) (-6969373212 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14154118671 / 1000000000000) (14154118782 / 1000000000000)
      | 1 => orderedInterval (-4480870357 / 1000000000000) (-4480865028 / 1000000000000)
      | 2 => orderedInterval (-82073613 / 1000000000000) (-82073596 / 1000000000000)
      | 3 => orderedInterval (236812618 / 1000000000000) (236812759 / 1000000000000)
      | 4 => orderedInterval (1936070636 / 1000000000000) (1936071797 / 1000000000000)
      | 5 => orderedInterval (-2412851138 / 1000000000000) (-2412843878 / 1000000000000)
      | 6 => orderedInterval (-2497963804 / 1000000000000) (-2497963726 / 1000000000000)
      | 7 => orderedInterval (-2784909792 / 1000000000000) (-2784909756 / 1000000000000)
      | _ => orderedInterval (5583209138 / 1000000000000) (5583212389 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13172302212 / 1000000000000) (13172302342 / 1000000000000)
      | 1 => orderedInterval (3180680923 / 1000000000000) (3180688533 / 1000000000000)
      | 2 => orderedInterval (-565012019 / 1000000000000) (-565011989 / 1000000000000)
      | 3 => orderedInterval (23600864862 / 1000000000000) (23600865158 / 1000000000000)
      | 4 => orderedInterval (-5406807123 / 1000000000000) (-5406804686 / 1000000000000)
      | 5 => orderedInterval (2033519802 / 1000000000000) (2033529794 / 1000000000000)
      | 6 => orderedInterval (-1153269215 / 1000000000000) (-1153269143 / 1000000000000)
      | 7 => orderedInterval (-4466776131 / 1000000000000) (-4466776098 / 1000000000000)
      | _ => orderedInterval (4777912497 / 1000000000000) (4777918501 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15176842452 / 1000000000000) (-15176842298 / 1000000000000)
      | 1 => orderedInterval (5901558264 / 1000000000000) (5901569800 / 1000000000000)
      | 2 => orderedInterval (928721845 / 1000000000000) (928721898 / 1000000000000)
      | 3 => orderedInterval (2837392338 / 1000000000000) (2837392976 / 1000000000000)
      | 4 => orderedInterval (-5479914379 / 1000000000000) (-5479909227 / 1000000000000)
      | 5 => orderedInterval (5097767752 / 1000000000000) (5097781881 / 1000000000000)
      | 6 => orderedInterval (4724886493 / 1000000000000) (4724886562 / 1000000000000)
      | 7 => orderedInterval (1558492827 / 1000000000000) (1558492860 / 1000000000000)
      | _ => orderedInterval (-4121214193 / 1000000000000) (-4121203058 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13090510358 / 1000000000000) (-13090510176 / 1000000000000)
      | 1 => orderedInterval (-6019191753 / 1000000000000) (-6019173910 / 1000000000000)
      | 2 => orderedInterval (4440629986 / 1000000000000) (4440630082 / 1000000000000)
      | 3 => orderedInterval (-108794186001 / 1000000000000) (-108794184599 / 1000000000000)
      | 4 => orderedInterval (14038186534 / 1000000000000) (14038197451 / 1000000000000)
      | 5 => orderedInterval (-4694062335 / 1000000000000) (-4694041814 / 1000000000000)
      | 6 => orderedInterval (1712290351 / 1000000000000) (1712290417 / 1000000000000)
      | 7 => orderedInterval (4563622506 / 1000000000000) (4563622540 / 1000000000000)
      | _ => orderedInterval (-12853753581 / 1000000000000) (-12853732935 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16645272609 / 1000000000000) (16645272826 / 1000000000000)
      | 1 => orderedInterval (-13069518921 / 1000000000000) (-13069491031 / 1000000000000)
      | 2 => orderedInterval (-4944148346 / 1000000000000) (-4944148169 / 1000000000000)
      | 3 => orderedInterval (-19414304011 / 1000000000000) (-19414300893 / 1000000000000)
      | 4 => orderedInterval (17412329725 / 1000000000000) (17412352959 / 1000000000000)
      | 5 => orderedInterval (-12437349927 / 1000000000000) (-12437319067 / 1000000000000)
      | 6 => orderedInterval (-5944530441 / 1000000000000) (-5944530375 / 1000000000000)
      | 7 => orderedInterval (-1421016828 / 1000000000000) (-1421016793 / 1000000000000)
      | _ => orderedInterval (-8363850661 / 1000000000000) (-8363812277 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (9651542359 / 1000000000000) (9651559743 / 1000000000000)
    | 1 => orderedInterval (35173415808 / 1000000000000) (35173442412 / 1000000000000)
    | 2 => orderedInterval (-3729151505 / 1000000000000) (-3729108606 / 1000000000000)
    | 3 => orderedInterval (-120696974651 / 1000000000000) (-120696902944 / 1000000000000)
    | _ => orderedInterval (-31537116801 / 1000000000000) (-31536992820 / 1000000000000)

theorem compactCertificate430_stateChecks0 :
    compactCertificate430.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (603 / 2)) (orderedInterval (29323560058 / 1000000000000) (29323560059 / 1000000000000), orderedInterval (35329863162 / 1000000000000) (35329863163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (888334141584303 / 4000000000000)) (orderedInterval (9833180864 / 1000000000000) (9833180908 / 1000000000000), orderedInterval (-52651914259 / 1000000000000) (-52651914215 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (287269009411599 / 800000000000)) (orderedInterval (41574854122 / 1000000000000) (41574855629 / 1000000000000), orderedInterval (-6722569019 / 1000000000000) (-6722567512 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_stateChecks1 :
    compactCertificate430.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (259213686977421 / 4000000000000)) (orderedInterval (37365883670 / 1000000000000) (37365885367 / 1000000000000), orderedInterval (-92091664140 / 1000000000000) (-92091662442 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (696284424642537 / 4000000000000)) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1890547659514629 / 4000000000000)) (orderedInterval (30032165857 / 1000000000000) (30032230058 / 1000000000000), orderedInterval (-21127297185 / 1000000000000) (-21127232984 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_stateChecks2 :
    compactCertificate430.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1392568849285677 / 4000000000000)) (orderedInterval (-8933759475 / 1000000000000) (-8933759474 / 1000000000000), orderedInterval (-41805939695 / 1000000000000) (-41805939694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2386190458826721 / 4000000000000)) (orderedInterval (13624088091 / 1000000000000) (13624088092 / 1000000000000), orderedInterval (29679621832 / 1000000000000) (29679621833 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1757657091954339 / 4000000000000)) (orderedInterval (13991534438 / 1000000000000) (13991534439 / 1000000000000), orderedInterval (35382234616 / 1000000000000) (35382234617 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_stateChecks3 :
    compactCertificate430.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2696697980864397 / 4000000000000)) (orderedInterval (14264072419 / 1000000000000) (14264072538 / 1000000000000), orderedInterval (-27228801403 / 1000000000000) (-27228801284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1556939305175013 / 4000000000000)) (orderedInterval (18041644282 / 1000000000000) (18041644283 / 1000000000000), orderedInterval (36171675150 / 1000000000000) (36171675151 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2762816118707817 / 4000000000000)) (orderedInterval (10091940239 / 1000000000000) (10091940240 / 1000000000000), orderedInterval (28625714625 / 1000000000000) (28625714626 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_stateChecks4 :
    compactCertificate430.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2581381201177773 / 4000000000000)) (orderedInterval (-27048121746 / 1000000000000) (-27048062049 / 1000000000000), orderedInterval (15985882179 / 1000000000000) (15985941877 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1842195429371709 / 4000000000000)) (orderedInterval (17173145031 / 1000000000000) (17173145510 / 1000000000000), orderedInterval (-32994245272 / 1000000000000) (-32994244792 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2088853273927611 / 4000000000000)) (orderedInterval (34812667011 / 1000000000000) (34812667238 / 1000000000000), orderedInterval (2642033237 / 1000000000000) (2642033464 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_stateChecks5 :
    compactCertificate430.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1741468085899659 / 4000000000000)) (orderedInterval (19306467646 / 1000000000000) (19306468668 / 1000000000000), orderedInterval (-33030062163 / 1000000000000) (-33030061142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1538639867320839 / 4000000000000)) (orderedInterval (33577557972 / 1000000000000) (33577662083 / 1000000000000), orderedInterval (-23012437367 / 1000000000000) (-23012333257 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (445957804919061 / 800000000000)) (orderedInterval (-27896391695 / 1000000000000) (-27896342444 / 1000000000000), orderedInterval (19099047362 / 1000000000000) (19099096613 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_stateChecks6 :
    compactCertificate430.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1233542757879567 / 4000000000000)) (orderedInterval (43713240379 / 1000000000000) (43713240382 / 1000000000000), orderedInterval (12319143826 / 1000000000000) (12319143828 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1045687856966487 / 4000000000000)) (orderedInterval (-49015669342 / 1000000000000) (-49015669323 / 1000000000000), orderedInterval (-5622804523 / 1000000000000) (-5622804504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (654342908045661 / 4000000000000)) (orderedInterval (52746243755 / 1000000000000) (52746243756 / 1000000000000), orderedInterval (33147705963 / 1000000000000) (33147705964 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_stateChecks7 :
    compactCertificate430.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (351907792193187 / 4000000000000)) (orderedInterval (60804220168 / 1000000000000) (60804220169 / 1000000000000), orderedInterval (59144402653 / 1000000000000) (59144402654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (955498111620561 / 4000000000000)) (orderedInterval (40386102402 / 1000000000000) (40386102403 / 1000000000000), orderedInterval (32071983703 / 1000000000000) (32071983704 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1304650983371697 / 4000000000000)) (orderedInterval (9732904496 / 1000000000000) (9732904497 / 1000000000000), orderedInterval (43079390554 / 1000000000000) (43079390555 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_stateChecks8 :
    compactCertificate430.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (551657091954339 / 4000000000000)) (orderedInterval (30690198943 / 1000000000000) (30690198944 / 1000000000000), orderedInterval (60503783111 / 1000000000000) (60503783112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2242455451708419 / 4000000000000)) (orderedInterval (27333001723 / 1000000000000) (27333040581 / 1000000000000), orderedInterval (-19734343672 / 1000000000000) (-19734304813 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1497856317243021 / 4000000000000)) (orderedInterval (-40629418422 / 1000000000000) (-40629418402 / 1000000000000), orderedInterval (-6969373232 / 1000000000000) (-6969373212 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_states : ∀ j,
    BesselStateValid (compactCertificate430.point j) (compactCertificate430.state j) :=
  compactCertificate430.statesValid_of_checks3 compactCertificate430_stateChecks0
    compactCertificate430_stateChecks1 compactCertificate430_stateChecks2
    compactCertificate430_stateChecks3 compactCertificate430_stateChecks4
    compactCertificate430_stateChecks5 compactCertificate430_stateChecks6
    compactCertificate430_stateChecks7 compactCertificate430_stateChecks8

theorem compactCertificate430_chunkChecks0_0 :
    compactCertificate430.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (603 / 2) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29323560058 / 1000000000000) (29323560059 / 1000000000000), orderedInterval (35329863162 / 1000000000000) (35329863163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (888334141584303 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9833180864 / 1000000000000) (9833180908 / 1000000000000), orderedInterval (-52651914259 / 1000000000000) (-52651914215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (287269009411599 / 800000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41574854122 / 1000000000000) (41574855629 / 1000000000000), orderedInterval (-6722569019 / 1000000000000) (-6722567512 / 1000000000000)))) (orderedInterval (14154118671 / 1000000000000) (14154118782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (259213686977421 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (37365883670 / 1000000000000) (37365885367 / 1000000000000), orderedInterval (-92091664140 / 1000000000000) (-92091662442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1890547659514629 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30032165857 / 1000000000000) (30032230058 / 1000000000000), orderedInterval (-21127297185 / 1000000000000) (-21127232984 / 1000000000000)))) (orderedInterval (-4480870357 / 1000000000000) (-4480865028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1392568849285677 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8933759475 / 1000000000000) (-8933759474 / 1000000000000), orderedInterval (-41805939695 / 1000000000000) (-41805939694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2386190458826721 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13624088091 / 1000000000000) (13624088092 / 1000000000000), orderedInterval (29679621832 / 1000000000000) (29679621833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1757657091954339 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13991534438 / 1000000000000) (13991534439 / 1000000000000), orderedInterval (35382234616 / 1000000000000) (35382234617 / 1000000000000)))) (orderedInterval (-82073613 / 1000000000000) (-82073596 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks0_1 :
    compactCertificate430.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2696697980864397 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14264072419 / 1000000000000) (14264072538 / 1000000000000), orderedInterval (-27228801403 / 1000000000000) (-27228801284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1556939305175013 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (18041644282 / 1000000000000) (18041644283 / 1000000000000), orderedInterval (36171675150 / 1000000000000) (36171675151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2762816118707817 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10091940239 / 1000000000000) (10091940240 / 1000000000000), orderedInterval (28625714625 / 1000000000000) (28625714626 / 1000000000000)))) (orderedInterval (236812618 / 1000000000000) (236812759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2581381201177773 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27048121746 / 1000000000000) (-27048062049 / 1000000000000), orderedInterval (15985882179 / 1000000000000) (15985941877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1842195429371709 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173145031 / 1000000000000) (17173145510 / 1000000000000), orderedInterval (-32994245272 / 1000000000000) (-32994244792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2088853273927611 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34812667011 / 1000000000000) (34812667238 / 1000000000000), orderedInterval (2642033237 / 1000000000000) (2642033464 / 1000000000000)))) (orderedInterval (1936070636 / 1000000000000) (1936071797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1741468085899659 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19306467646 / 1000000000000) (19306468668 / 1000000000000), orderedInterval (-33030062163 / 1000000000000) (-33030061142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1538639867320839 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33577557972 / 1000000000000) (33577662083 / 1000000000000), orderedInterval (-23012437367 / 1000000000000) (-23012333257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (445957804919061 / 800000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27896391695 / 1000000000000) (-27896342444 / 1000000000000), orderedInterval (19099047362 / 1000000000000) (19099096613 / 1000000000000)))) (orderedInterval (-2412851138 / 1000000000000) (-2412843878 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks0_2 :
    compactCertificate430.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1233542757879567 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43713240379 / 1000000000000) (43713240382 / 1000000000000), orderedInterval (12319143826 / 1000000000000) (12319143828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1045687856966487 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49015669342 / 1000000000000) (-49015669323 / 1000000000000), orderedInterval (-5622804523 / 1000000000000) (-5622804504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (654342908045661 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52746243755 / 1000000000000) (52746243756 / 1000000000000), orderedInterval (33147705963 / 1000000000000) (33147705964 / 1000000000000)))) (orderedInterval (-2497963804 / 1000000000000) (-2497963726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (351907792193187 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60804220168 / 1000000000000) (60804220169 / 1000000000000), orderedInterval (59144402653 / 1000000000000) (59144402654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (955498111620561 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40386102402 / 1000000000000) (40386102403 / 1000000000000), orderedInterval (32071983703 / 1000000000000) (32071983704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1304650983371697 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9732904496 / 1000000000000) (9732904497 / 1000000000000), orderedInterval (43079390554 / 1000000000000) (43079390555 / 1000000000000)))) (orderedInterval (-2784909792 / 1000000000000) (-2784909756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (551657091954339 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (30690198943 / 1000000000000) (30690198944 / 1000000000000), orderedInterval (60503783111 / 1000000000000) (60503783112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2242455451708419 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27333001723 / 1000000000000) (27333040581 / 1000000000000), orderedInterval (-19734343672 / 1000000000000) (-19734304813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1497856317243021 / 4000000000000) 0 (IntervalRat.scale (603 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40629418422 / 1000000000000) (-40629418402 / 1000000000000), orderedInterval (-6969373232 / 1000000000000) (-6969373212 / 1000000000000)))) (orderedInterval (5583209138 / 1000000000000) (5583212389 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks0 :
    compactCertificate430.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate430.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate430_chunkChecks0_0
    compactCertificate430_chunkChecks0_1 compactCertificate430_chunkChecks0_2

theorem compactCertificate430_chunkChecks1_0 :
    compactCertificate430.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (603 / 2) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29323560058 / 1000000000000) (29323560059 / 1000000000000), orderedInterval (35329863162 / 1000000000000) (35329863163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (888334141584303 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9833180864 / 1000000000000) (9833180908 / 1000000000000), orderedInterval (-52651914259 / 1000000000000) (-52651914215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (287269009411599 / 800000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41574854122 / 1000000000000) (41574855629 / 1000000000000), orderedInterval (-6722569019 / 1000000000000) (-6722567512 / 1000000000000)))) (orderedInterval (13172302212 / 1000000000000) (13172302342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (259213686977421 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (37365883670 / 1000000000000) (37365885367 / 1000000000000), orderedInterval (-92091664140 / 1000000000000) (-92091662442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1890547659514629 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30032165857 / 1000000000000) (30032230058 / 1000000000000), orderedInterval (-21127297185 / 1000000000000) (-21127232984 / 1000000000000)))) (orderedInterval (3180680923 / 1000000000000) (3180688533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1392568849285677 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8933759475 / 1000000000000) (-8933759474 / 1000000000000), orderedInterval (-41805939695 / 1000000000000) (-41805939694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2386190458826721 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13624088091 / 1000000000000) (13624088092 / 1000000000000), orderedInterval (29679621832 / 1000000000000) (29679621833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1757657091954339 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13991534438 / 1000000000000) (13991534439 / 1000000000000), orderedInterval (35382234616 / 1000000000000) (35382234617 / 1000000000000)))) (orderedInterval (-565012019 / 1000000000000) (-565011989 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks1_1 :
    compactCertificate430.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2696697980864397 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14264072419 / 1000000000000) (14264072538 / 1000000000000), orderedInterval (-27228801403 / 1000000000000) (-27228801284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1556939305175013 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (18041644282 / 1000000000000) (18041644283 / 1000000000000), orderedInterval (36171675150 / 1000000000000) (36171675151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2762816118707817 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10091940239 / 1000000000000) (10091940240 / 1000000000000), orderedInterval (28625714625 / 1000000000000) (28625714626 / 1000000000000)))) (orderedInterval (23600864862 / 1000000000000) (23600865158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2581381201177773 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27048121746 / 1000000000000) (-27048062049 / 1000000000000), orderedInterval (15985882179 / 1000000000000) (15985941877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1842195429371709 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173145031 / 1000000000000) (17173145510 / 1000000000000), orderedInterval (-32994245272 / 1000000000000) (-32994244792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2088853273927611 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34812667011 / 1000000000000) (34812667238 / 1000000000000), orderedInterval (2642033237 / 1000000000000) (2642033464 / 1000000000000)))) (orderedInterval (-5406807123 / 1000000000000) (-5406804686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1741468085899659 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19306467646 / 1000000000000) (19306468668 / 1000000000000), orderedInterval (-33030062163 / 1000000000000) (-33030061142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1538639867320839 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33577557972 / 1000000000000) (33577662083 / 1000000000000), orderedInterval (-23012437367 / 1000000000000) (-23012333257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (445957804919061 / 800000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27896391695 / 1000000000000) (-27896342444 / 1000000000000), orderedInterval (19099047362 / 1000000000000) (19099096613 / 1000000000000)))) (orderedInterval (2033519802 / 1000000000000) (2033529794 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks1_2 :
    compactCertificate430.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1233542757879567 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43713240379 / 1000000000000) (43713240382 / 1000000000000), orderedInterval (12319143826 / 1000000000000) (12319143828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1045687856966487 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49015669342 / 1000000000000) (-49015669323 / 1000000000000), orderedInterval (-5622804523 / 1000000000000) (-5622804504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (654342908045661 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52746243755 / 1000000000000) (52746243756 / 1000000000000), orderedInterval (33147705963 / 1000000000000) (33147705964 / 1000000000000)))) (orderedInterval (-1153269215 / 1000000000000) (-1153269143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (351907792193187 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60804220168 / 1000000000000) (60804220169 / 1000000000000), orderedInterval (59144402653 / 1000000000000) (59144402654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (955498111620561 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40386102402 / 1000000000000) (40386102403 / 1000000000000), orderedInterval (32071983703 / 1000000000000) (32071983704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1304650983371697 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9732904496 / 1000000000000) (9732904497 / 1000000000000), orderedInterval (43079390554 / 1000000000000) (43079390555 / 1000000000000)))) (orderedInterval (-4466776131 / 1000000000000) (-4466776098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (551657091954339 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (30690198943 / 1000000000000) (30690198944 / 1000000000000), orderedInterval (60503783111 / 1000000000000) (60503783112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2242455451708419 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27333001723 / 1000000000000) (27333040581 / 1000000000000), orderedInterval (-19734343672 / 1000000000000) (-19734304813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1497856317243021 / 4000000000000) 1 (IntervalRat.scale (603 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40629418422 / 1000000000000) (-40629418402 / 1000000000000), orderedInterval (-6969373232 / 1000000000000) (-6969373212 / 1000000000000)))) (orderedInterval (4777912497 / 1000000000000) (4777918501 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks1 :
    compactCertificate430.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate430.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate430_chunkChecks1_0
    compactCertificate430_chunkChecks1_1 compactCertificate430_chunkChecks1_2

theorem compactCertificate430_chunkChecks2_0 :
    compactCertificate430.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (603 / 2) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29323560058 / 1000000000000) (29323560059 / 1000000000000), orderedInterval (35329863162 / 1000000000000) (35329863163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (888334141584303 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9833180864 / 1000000000000) (9833180908 / 1000000000000), orderedInterval (-52651914259 / 1000000000000) (-52651914215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (287269009411599 / 800000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41574854122 / 1000000000000) (41574855629 / 1000000000000), orderedInterval (-6722569019 / 1000000000000) (-6722567512 / 1000000000000)))) (orderedInterval (-15176842452 / 1000000000000) (-15176842298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (259213686977421 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (37365883670 / 1000000000000) (37365885367 / 1000000000000), orderedInterval (-92091664140 / 1000000000000) (-92091662442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1890547659514629 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30032165857 / 1000000000000) (30032230058 / 1000000000000), orderedInterval (-21127297185 / 1000000000000) (-21127232984 / 1000000000000)))) (orderedInterval (5901558264 / 1000000000000) (5901569800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1392568849285677 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8933759475 / 1000000000000) (-8933759474 / 1000000000000), orderedInterval (-41805939695 / 1000000000000) (-41805939694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2386190458826721 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13624088091 / 1000000000000) (13624088092 / 1000000000000), orderedInterval (29679621832 / 1000000000000) (29679621833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1757657091954339 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13991534438 / 1000000000000) (13991534439 / 1000000000000), orderedInterval (35382234616 / 1000000000000) (35382234617 / 1000000000000)))) (orderedInterval (928721845 / 1000000000000) (928721898 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks2_1 :
    compactCertificate430.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2696697980864397 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14264072419 / 1000000000000) (14264072538 / 1000000000000), orderedInterval (-27228801403 / 1000000000000) (-27228801284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1556939305175013 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (18041644282 / 1000000000000) (18041644283 / 1000000000000), orderedInterval (36171675150 / 1000000000000) (36171675151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2762816118707817 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10091940239 / 1000000000000) (10091940240 / 1000000000000), orderedInterval (28625714625 / 1000000000000) (28625714626 / 1000000000000)))) (orderedInterval (2837392338 / 1000000000000) (2837392976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2581381201177773 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27048121746 / 1000000000000) (-27048062049 / 1000000000000), orderedInterval (15985882179 / 1000000000000) (15985941877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1842195429371709 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173145031 / 1000000000000) (17173145510 / 1000000000000), orderedInterval (-32994245272 / 1000000000000) (-32994244792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2088853273927611 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34812667011 / 1000000000000) (34812667238 / 1000000000000), orderedInterval (2642033237 / 1000000000000) (2642033464 / 1000000000000)))) (orderedInterval (-5479914379 / 1000000000000) (-5479909227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1741468085899659 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19306467646 / 1000000000000) (19306468668 / 1000000000000), orderedInterval (-33030062163 / 1000000000000) (-33030061142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1538639867320839 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33577557972 / 1000000000000) (33577662083 / 1000000000000), orderedInterval (-23012437367 / 1000000000000) (-23012333257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (445957804919061 / 800000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27896391695 / 1000000000000) (-27896342444 / 1000000000000), orderedInterval (19099047362 / 1000000000000) (19099096613 / 1000000000000)))) (orderedInterval (5097767752 / 1000000000000) (5097781881 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks2_2 :
    compactCertificate430.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1233542757879567 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43713240379 / 1000000000000) (43713240382 / 1000000000000), orderedInterval (12319143826 / 1000000000000) (12319143828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1045687856966487 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49015669342 / 1000000000000) (-49015669323 / 1000000000000), orderedInterval (-5622804523 / 1000000000000) (-5622804504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (654342908045661 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52746243755 / 1000000000000) (52746243756 / 1000000000000), orderedInterval (33147705963 / 1000000000000) (33147705964 / 1000000000000)))) (orderedInterval (4724886493 / 1000000000000) (4724886562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (351907792193187 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60804220168 / 1000000000000) (60804220169 / 1000000000000), orderedInterval (59144402653 / 1000000000000) (59144402654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (955498111620561 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40386102402 / 1000000000000) (40386102403 / 1000000000000), orderedInterval (32071983703 / 1000000000000) (32071983704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1304650983371697 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9732904496 / 1000000000000) (9732904497 / 1000000000000), orderedInterval (43079390554 / 1000000000000) (43079390555 / 1000000000000)))) (orderedInterval (1558492827 / 1000000000000) (1558492860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (551657091954339 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (30690198943 / 1000000000000) (30690198944 / 1000000000000), orderedInterval (60503783111 / 1000000000000) (60503783112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2242455451708419 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27333001723 / 1000000000000) (27333040581 / 1000000000000), orderedInterval (-19734343672 / 1000000000000) (-19734304813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1497856317243021 / 4000000000000) 2 (IntervalRat.scale (603 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40629418422 / 1000000000000) (-40629418402 / 1000000000000), orderedInterval (-6969373232 / 1000000000000) (-6969373212 / 1000000000000)))) (orderedInterval (-4121214193 / 1000000000000) (-4121203058 / 1000000000000))) = true
  rfl'

theorem compactCertificate430_chunkChecks2 :
    compactCertificate430.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate430.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate430_chunkChecks2_0
    compactCertificate430_chunkChecks2_1 compactCertificate430_chunkChecks2_2

theorem compactCertificate430_chunkChecks3_0 :
    compactCertificate430.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (603 / 2) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29323560058 / 1000000000000) (29323560059 / 1000000000000), orderedInterval (35329863162 / 1000000000000) (35329863163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (888334141584303 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9833180864 / 1000000000000) (9833180908 / 1000000000000), orderedInterval (-52651914259 / 1000000000000) (-52651914215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (287269009411599 / 800000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41574854122 / 1000000000000) (41574855629 / 1000000000000), orderedInterval (-6722569019 / 1000000000000) (-6722567512 / 1000000000000)))) (orderedInterval (-13090510358 / 1000000000000) (-13090510176 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (259213686977421 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (37365883670 / 1000000000000) (37365885367 / 1000000000000), orderedInterval (-92091664140 / 1000000000000) (-92091662442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1890547659514629 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30032165857 / 1000000000000) (30032230058 / 1000000000000), orderedInterval (-21127297185 / 1000000000000) (-21127232984 / 1000000000000)))) (orderedInterval (-6019191753 / 1000000000000) (-6019173910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1392568849285677 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8933759475 / 1000000000000) (-8933759474 / 1000000000000), orderedInterval (-41805939695 / 1000000000000) (-41805939694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2386190458826721 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13624088091 / 1000000000000) (13624088092 / 1000000000000), orderedInterval (29679621832 / 1000000000000) (29679621833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1757657091954339 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13991534438 / 1000000000000) (13991534439 / 1000000000000), orderedInterval (35382234616 / 1000000000000) (35382234617 / 1000000000000)))) (orderedInterval (4440629986 / 1000000000000) (4440630082 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate430_chunkChecks3_1 :
    compactCertificate430.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2696697980864397 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14264072419 / 1000000000000) (14264072538 / 1000000000000), orderedInterval (-27228801403 / 1000000000000) (-27228801284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1556939305175013 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (18041644282 / 1000000000000) (18041644283 / 1000000000000), orderedInterval (36171675150 / 1000000000000) (36171675151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2762816118707817 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10091940239 / 1000000000000) (10091940240 / 1000000000000), orderedInterval (28625714625 / 1000000000000) (28625714626 / 1000000000000)))) (orderedInterval (-108794186001 / 1000000000000) (-108794184599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2581381201177773 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27048121746 / 1000000000000) (-27048062049 / 1000000000000), orderedInterval (15985882179 / 1000000000000) (15985941877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1842195429371709 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173145031 / 1000000000000) (17173145510 / 1000000000000), orderedInterval (-32994245272 / 1000000000000) (-32994244792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2088853273927611 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34812667011 / 1000000000000) (34812667238 / 1000000000000), orderedInterval (2642033237 / 1000000000000) (2642033464 / 1000000000000)))) (orderedInterval (14038186534 / 1000000000000) (14038197451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1741468085899659 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19306467646 / 1000000000000) (19306468668 / 1000000000000), orderedInterval (-33030062163 / 1000000000000) (-33030061142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1538639867320839 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33577557972 / 1000000000000) (33577662083 / 1000000000000), orderedInterval (-23012437367 / 1000000000000) (-23012333257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (445957804919061 / 800000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27896391695 / 1000000000000) (-27896342444 / 1000000000000), orderedInterval (19099047362 / 1000000000000) (19099096613 / 1000000000000)))) (orderedInterval (-4694062335 / 1000000000000) (-4694041814 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate430_chunkChecks3_2 :
    compactCertificate430.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1233542757879567 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43713240379 / 1000000000000) (43713240382 / 1000000000000), orderedInterval (12319143826 / 1000000000000) (12319143828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1045687856966487 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49015669342 / 1000000000000) (-49015669323 / 1000000000000), orderedInterval (-5622804523 / 1000000000000) (-5622804504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (654342908045661 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52746243755 / 1000000000000) (52746243756 / 1000000000000), orderedInterval (33147705963 / 1000000000000) (33147705964 / 1000000000000)))) (orderedInterval (1712290351 / 1000000000000) (1712290417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (351907792193187 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60804220168 / 1000000000000) (60804220169 / 1000000000000), orderedInterval (59144402653 / 1000000000000) (59144402654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (955498111620561 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40386102402 / 1000000000000) (40386102403 / 1000000000000), orderedInterval (32071983703 / 1000000000000) (32071983704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1304650983371697 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9732904496 / 1000000000000) (9732904497 / 1000000000000), orderedInterval (43079390554 / 1000000000000) (43079390555 / 1000000000000)))) (orderedInterval (4563622506 / 1000000000000) (4563622540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (551657091954339 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (30690198943 / 1000000000000) (30690198944 / 1000000000000), orderedInterval (60503783111 / 1000000000000) (60503783112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2242455451708419 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27333001723 / 1000000000000) (27333040581 / 1000000000000), orderedInterval (-19734343672 / 1000000000000) (-19734304813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1497856317243021 / 4000000000000) 3 (IntervalRat.scale (603 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40629418422 / 1000000000000) (-40629418402 / 1000000000000), orderedInterval (-6969373232 / 1000000000000) (-6969373212 / 1000000000000)))) (orderedInterval (-12853753581 / 1000000000000) (-12853732935 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate430_chunkChecks3 :
    compactCertificate430.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate430.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate430_chunkChecks3_0
    compactCertificate430_chunkChecks3_1 compactCertificate430_chunkChecks3_2

theorem compactCertificate430_chunkChecks4_0 :
    compactCertificate430.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (603 / 2) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29323560058 / 1000000000000) (29323560059 / 1000000000000), orderedInterval (35329863162 / 1000000000000) (35329863163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (888334141584303 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9833180864 / 1000000000000) (9833180908 / 1000000000000), orderedInterval (-52651914259 / 1000000000000) (-52651914215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (287269009411599 / 800000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41574854122 / 1000000000000) (41574855629 / 1000000000000), orderedInterval (-6722569019 / 1000000000000) (-6722567512 / 1000000000000)))) (orderedInterval (16645272609 / 1000000000000) (16645272826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (259213686977421 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (37365883670 / 1000000000000) (37365885367 / 1000000000000), orderedInterval (-92091664140 / 1000000000000) (-92091662442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (696284424642537 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53147185073 / 1000000000000) (-53147165633 / 1000000000000), orderedInterval (29007617445 / 1000000000000) (29007636885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1890547659514629 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30032165857 / 1000000000000) (30032230058 / 1000000000000), orderedInterval (-21127297185 / 1000000000000) (-21127232984 / 1000000000000)))) (orderedInterval (-13069518921 / 1000000000000) (-13069491031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1392568849285677 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8933759475 / 1000000000000) (-8933759474 / 1000000000000), orderedInterval (-41805939695 / 1000000000000) (-41805939694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2386190458826721 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13624088091 / 1000000000000) (13624088092 / 1000000000000), orderedInterval (29679621832 / 1000000000000) (29679621833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1757657091954339 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13991534438 / 1000000000000) (13991534439 / 1000000000000), orderedInterval (35382234616 / 1000000000000) (35382234617 / 1000000000000)))) (orderedInterval (-4944148346 / 1000000000000) (-4944148169 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate430_chunkChecks4_1 :
    compactCertificate430.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2696697980864397 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14264072419 / 1000000000000) (14264072538 / 1000000000000), orderedInterval (-27228801403 / 1000000000000) (-27228801284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1556939305175013 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (18041644282 / 1000000000000) (18041644283 / 1000000000000), orderedInterval (36171675150 / 1000000000000) (36171675151 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2762816118707817 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10091940239 / 1000000000000) (10091940240 / 1000000000000), orderedInterval (28625714625 / 1000000000000) (28625714626 / 1000000000000)))) (orderedInterval (-19414304011 / 1000000000000) (-19414300893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2581381201177773 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27048121746 / 1000000000000) (-27048062049 / 1000000000000), orderedInterval (15985882179 / 1000000000000) (15985941877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1842195429371709 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17173145031 / 1000000000000) (17173145510 / 1000000000000), orderedInterval (-32994245272 / 1000000000000) (-32994244792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2088853273927611 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34812667011 / 1000000000000) (34812667238 / 1000000000000), orderedInterval (2642033237 / 1000000000000) (2642033464 / 1000000000000)))) (orderedInterval (17412329725 / 1000000000000) (17412352959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1741468085899659 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19306467646 / 1000000000000) (19306468668 / 1000000000000), orderedInterval (-33030062163 / 1000000000000) (-33030061142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1538639867320839 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33577557972 / 1000000000000) (33577662083 / 1000000000000), orderedInterval (-23012437367 / 1000000000000) (-23012333257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (445957804919061 / 800000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27896391695 / 1000000000000) (-27896342444 / 1000000000000), orderedInterval (19099047362 / 1000000000000) (19099096613 / 1000000000000)))) (orderedInterval (-12437349927 / 1000000000000) (-12437319067 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate430_chunkChecks4_2 :
    compactCertificate430.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1233542757879567 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43713240379 / 1000000000000) (43713240382 / 1000000000000), orderedInterval (12319143826 / 1000000000000) (12319143828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1045687856966487 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-49015669342 / 1000000000000) (-49015669323 / 1000000000000), orderedInterval (-5622804523 / 1000000000000) (-5622804504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (654342908045661 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52746243755 / 1000000000000) (52746243756 / 1000000000000), orderedInterval (33147705963 / 1000000000000) (33147705964 / 1000000000000)))) (orderedInterval (-5944530441 / 1000000000000) (-5944530375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (351907792193187 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60804220168 / 1000000000000) (60804220169 / 1000000000000), orderedInterval (59144402653 / 1000000000000) (59144402654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (955498111620561 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (40386102402 / 1000000000000) (40386102403 / 1000000000000), orderedInterval (32071983703 / 1000000000000) (32071983704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1304650983371697 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9732904496 / 1000000000000) (9732904497 / 1000000000000), orderedInterval (43079390554 / 1000000000000) (43079390555 / 1000000000000)))) (orderedInterval (-1421016828 / 1000000000000) (-1421016793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (551657091954339 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (30690198943 / 1000000000000) (30690198944 / 1000000000000), orderedInterval (60503783111 / 1000000000000) (60503783112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2242455451708419 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27333001723 / 1000000000000) (27333040581 / 1000000000000), orderedInterval (-19734343672 / 1000000000000) (-19734304813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1497856317243021 / 4000000000000) 4 (IntervalRat.scale (603 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40629418422 / 1000000000000) (-40629418402 / 1000000000000), orderedInterval (-6969373232 / 1000000000000) (-6969373212 / 1000000000000)))) (orderedInterval (-8363850661 / 1000000000000) (-8363812277 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate430_chunkChecks4 :
    compactCertificate430.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate430.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate430_chunkChecks4_0
    compactCertificate430_chunkChecks4_1 compactCertificate430_chunkChecks4_2

theorem compactCertificate430_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate430.chunkCheck r b = true :=
  compactCertificate430.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate430_chunkChecks0
    · exact compactCertificate430_chunkChecks1
    · exact compactCertificate430_chunkChecks2
    · exact compactCertificate430_chunkChecks3
    · exact compactCertificate430_chunkChecks4)

theorem compactCertificate430_coefficient0 :
    compactCertificate430.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate430_coefficient1 :
    compactCertificate430.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate430_coefficient2 :
    compactCertificate430.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate430_coefficient3 :
    compactCertificate430.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate430_coefficient4 :
    compactCertificate430.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate430_coefficients : ∀ r : Fin 5,
    compactCertificate430.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate430_coefficient0
  · exact compactCertificate430_coefficient1
  · exact compactCertificate430_coefficient2
  · exact compactCertificate430_coefficient3
  · exact compactCertificate430_coefficient4

theorem compactCertificate430_lower : (1 : ℚ) ≤ compactCertificate430.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate430, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate430_proves {t : ℝ} (ht : t ∈ compactCertificate430.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate430.proves compactCertificate430_states compactCertificate430_chunks
    compactCertificate430_coefficients compactCertificate430_lower ht

end Erdos232
