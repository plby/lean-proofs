/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate512 : CompactCertificate where
  left := 383
  right := 384
  center := 767 / 2
  grid := fun i =>
    match i.val with
    | 0 => 122
    | 1 => 90
    | 2 => 145
    | 3 => 26
    | 4 => 71
    | 5 => 191
    | 6 => 141
    | 7 => 242
    | 8 => 178
    | 9 => 273
    | 10 => 158
    | 11 => 280
    | 12 => 261
    | 13 => 187
    | 14 => 212
    | 15 => 176
    | 16 => 156
    | 17 => 226
    | 18 => 125
    | 19 => 106
    | 20 => 66
    | 21 => 36
    | 22 => 97
    | 23 => 132
    | 24 => 56
    | 25 => 227
    | _ => 152
  point := fun i =>
    match i.val with
    | 0 => 767 / 2
    | 1 => 1129937457040067 / 4000000000000
    | 2 => 365398557576611 / 800000000000
    | 3 => 329712931860169 / 4000000000000
    | 4 => 885655312936693 / 4000000000000
    | 5 => 2404726459117281 / 4000000000000
    | 6 => 1771310625874153 / 4000000000000
    | 7 => 3035170948457869 / 4000000000000
    | 8 => 2235693183298471 / 4000000000000
    | 9 => 3430128277484233 / 4000000000000
    | 10 => 1980385484360257 / 4000000000000
    | 11 => 3514228794442613 / 4000000000000
    | 12 => 3283448393537897 / 4000000000000
    | 13 => 2343223705353401 / 4000000000000
    | 14 => 2656965938810079 / 4000000000000
    | 15 => 2215101197155951 / 4000000000000
    | 16 => 1957109084966971 / 4000000000000
    | 17 => 567246494814129 / 800000000000
    | 18 => 1569033657203363 / 4000000000000
    | 19 => 1330087207783243 / 4000000000000
    | 20 => 832306816701529 / 4000000000000
    | 21 => 447617374149543 / 4000000000000
    | 22 => 1215368244797629 / 4000000000000
    | 23 => 1659481433243933 / 4000000000000
    | 24 => 701693183298471 / 4000000000000
    | 25 => 2852343833267591 / 4000000000000
    | _ => 1905233491418569 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (34519445285 / 1000000000000) (34519445286 / 1000000000000), orderedInterval (21598301898 / 1000000000000) (21598301899 / 1000000000000))
    | 1 => (orderedInterval (23834148195 / 1000000000000) (23834148196 / 1000000000000), orderedInterval (41013643533 / 1000000000000) (41013643534 / 1000000000000))
    | 2 => (orderedInterval (-33910316827 / 1000000000000) (-33910277243 / 1000000000000), orderedInterval (15654406512 / 1000000000000) (15654446096 / 1000000000000))
    | 3 => (orderedInterval (87811009239 / 1000000000000) (87811009255 / 1000000000000), orderedInterval (2989711666 / 1000000000000) (2989711682 / 1000000000000))
    | 4 => (orderedInterval (40440477110 / 1000000000000) (40440555381 / 1000000000000), orderedInterval (-35302324721 / 1000000000000) (-35302246451 / 1000000000000))
    | 5 => (orderedInterval (-30548317665 / 1000000000000) (-30548280357 / 1000000000000), orderedInterval (11239157302 / 1000000000000) (11239194610 / 1000000000000))
    | 6 => (orderedInterval (-22892128809 / 1000000000000) (-22892128808 / 1000000000000), orderedInterval (-30199554348 / 1000000000000) (-30199554347 / 1000000000000))
    | 7 => (orderedInterval (-18380518988 / 1000000000000) (-18380518034 / 1000000000000), orderedInterval (22398421944 / 1000000000000) (22398422899 / 1000000000000))
    | 8 => (orderedInterval (16327478933 / 1000000000000) (16327478934 / 1000000000000), orderedInterval (29522229412 / 1000000000000) (29522229413 / 1000000000000))
    | 9 => (orderedInterval (-16759793519 / 1000000000000) (-16759793518 / 1000000000000), orderedInterval (-21472669944 / 1000000000000) (-21472669943 / 1000000000000))
    | 10 => (orderedInterval (-16879929021 / 1000000000000) (-16879928585 / 1000000000000), orderedInterval (31654344132 / 1000000000000) (31654344569 / 1000000000000))
    | 11 => (orderedInterval (-8044700269 / 1000000000000) (-8044700267 / 1000000000000), orderedInterval (25693145880 / 1000000000000) (25693145882 / 1000000000000))
    | 12 => (orderedInterval (-27645540000 / 1000000000000) (-27645527888 / 1000000000000), orderedInterval (3374587569 / 1000000000000) (3374599681 / 1000000000000))
    | 13 => (orderedInterval (25548454368 / 1000000000000) (25548474362 / 1000000000000), orderedInterval (-20854906342 / 1000000000000) (-20854886348 / 1000000000000))
    | 14 => (orderedInterval (-25898044099 / 1000000000000) (-25898007821 / 1000000000000), orderedInterval (16981441623 / 1000000000000) (16981477901 / 1000000000000))
    | 15 => (orderedInterval (33824191653 / 1000000000000) (33824193326 / 1000000000000), orderedInterval (-2380641267 / 1000000000000) (-2380639594 / 1000000000000))
    | 16 => (orderedInterval (-939193068 / 1000000000000) (-939193066 / 1000000000000), orderedInterval (36060102164 / 1000000000000) (36060102165 / 1000000000000))
    | 17 => (orderedInterval (-4673179371 / 1000000000000) (-4673179369 / 1000000000000), orderedInterval (29600596580 / 1000000000000) (29600596582 / 1000000000000))
    | 18 => (orderedInterval (-13602287941 / 1000000000000) (-13602287940 / 1000000000000), orderedInterval (-37902826740 / 1000000000000) (-37902826739 / 1000000000000))
    | 19 => (orderedInterval (12847042367 / 1000000000000) (12847042368 / 1000000000000), orderedInterval (41807416614 / 1000000000000) (41807416615 / 1000000000000))
    | 20 => (orderedInterval (55231207368 / 1000000000000) (55231207401 / 1000000000000), orderedInterval (2875382191 / 1000000000000) (2875382223 / 1000000000000))
    | 21 => (orderedInterval (-29975844116 / 1000000000000) (-29975842436 / 1000000000000), orderedInterval (69347019750 / 1000000000000) (69347021430 / 1000000000000))
    | 22 => (orderedInterval (4908442089 / 1000000000000) (4908442096 / 1000000000000), orderedInterval (-45517883949 / 1000000000000) (-45517883942 / 1000000000000))
    | 23 => (orderedInterval (32206905744 / 1000000000000) (32206905745 / 1000000000000), orderedInterval (22259564209 / 1000000000000) (22259564210 / 1000000000000))
    | 24 => (orderedInterval (16578168664 / 1000000000000) (16578168665 / 1000000000000), orderedInterval (57868428889 / 1000000000000) (57868428890 / 1000000000000))
    | 25 => (orderedInterval (-19917715506 / 1000000000000) (-19917715505 / 1000000000000), orderedInterval (-22258255832 / 1000000000000) (-22258255831 / 1000000000000))
    | _ => (orderedInterval (-15193055783 / 1000000000000) (-15193055561 / 1000000000000), orderedInterval (33268650040 / 1000000000000) (33268650262 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11914491649 / 1000000000000) (11914493999 / 1000000000000)
      | 1 => orderedInterval (2695531496 / 1000000000000) (2695537053 / 1000000000000)
      | 2 => orderedInterval (961531657 / 1000000000000) (961531709 / 1000000000000)
      | 3 => orderedInterval (583747496 / 1000000000000) (583747681 / 1000000000000)
      | 4 => orderedInterval (3046080973 / 1000000000000) (3046083312 / 1000000000000)
      | 5 => orderedInterval (324685632 / 1000000000000) (324685689 / 1000000000000)
      | 6 => orderedInterval (3245827878 / 1000000000000) (3245827976 / 1000000000000)
      | 7 => orderedInterval (-2026150596 / 1000000000000) (-2026150519 / 1000000000000)
      | _ => orderedInterval (4571896270 / 1000000000000) (4571896419 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9936387496 / 1000000000000) (9936390293 / 1000000000000)
      | 1 => orderedInterval (-2003658941 / 1000000000000) (-2003653081 / 1000000000000)
      | 2 => orderedInterval (-327063431 / 1000000000000) (-327063335 / 1000000000000)
      | 3 => orderedInterval (19926701957 / 1000000000000) (19926702315 / 1000000000000)
      | 4 => orderedInterval (-3291678018 / 1000000000000) (-3291674269 / 1000000000000)
      | 5 => orderedInterval (-1271203766 / 1000000000000) (-1271203684 / 1000000000000)
      | 6 => orderedInterval (4197823838 / 1000000000000) (4197823928 / 1000000000000)
      | 7 => orderedInterval (-1400980159 / 1000000000000) (-1400980108 / 1000000000000)
      | _ => orderedInterval (-4224109976 / 1000000000000) (-4224109774 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11006085703 / 1000000000000) (-11006082366 / 1000000000000)
      | 1 => orderedInterval (-5779666547 / 1000000000000) (-5779658989 / 1000000000000)
      | 2 => orderedInterval (-3056764260 / 1000000000000) (-3056764078 / 1000000000000)
      | 3 => orderedInterval (-6855750153 / 1000000000000) (-6855749422 / 1000000000000)
      | 4 => orderedInterval (-8308359051 / 1000000000000) (-8308352954 / 1000000000000)
      | 5 => orderedInterval (-489581164 / 1000000000000) (-489581044 / 1000000000000)
      | 6 => orderedInterval (-2268975003 / 1000000000000) (-2268974917 / 1000000000000)
      | 7 => orderedInterval (2915056945 / 1000000000000) (2915056989 / 1000000000000)
      | _ => orderedInterval (-10012842188 / 1000000000000) (-10012841903 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10236704832 / 1000000000000) (-10236700858 / 1000000000000)
      | 1 => orderedInterval (3341383413 / 1000000000000) (3341394308 / 1000000000000)
      | 2 => orderedInterval (3150523860 / 1000000000000) (3150524210 / 1000000000000)
      | 3 => orderedInterval (-91599487914 / 1000000000000) (-91599486359 / 1000000000000)
      | 4 => orderedInterval (8094608893 / 1000000000000) (8094618954 / 1000000000000)
      | 5 => orderedInterval (-420762524 / 1000000000000) (-420762344 / 1000000000000)
      | 6 => orderedInterval (-4951629591 / 1000000000000) (-4951629508 / 1000000000000)
      | 7 => orderedInterval (1670395313 / 1000000000000) (1670395356 / 1000000000000)
      | _ => orderedInterval (303690489 / 1000000000000) (303690910 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9797153749 / 1000000000000) (9797158491 / 1000000000000)
      | 1 => orderedInterval (13259142729 / 1000000000000) (13259159287 / 1000000000000)
      | 2 => orderedInterval (10452705083 / 1000000000000) (10452705759 / 1000000000000)
      | 3 => orderedInterval (39955153915 / 1000000000000) (39955157303 / 1000000000000)
      | 4 => orderedInterval (24766687294 / 1000000000000) (24766704243 / 1000000000000)
      | 5 => orderedInterval (444562841 / 1000000000000) (444563119 / 1000000000000)
      | 6 => orderedInterval (2151132801 / 1000000000000) (2151132883 / 1000000000000)
      | 7 => orderedInterval (-3429098126 / 1000000000000) (-3429098080 / 1000000000000)
      | _ => orderedInterval (26167010003 / 1000000000000) (26167010649 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (25317642455 / 1000000000000) (25317653319 / 1000000000000)
    | 1 => orderedInterval (21542219000 / 1000000000000) (21542232285 / 1000000000000)
    | 2 => orderedInterval (-44862967124 / 1000000000000) (-44862948684 / 1000000000000)
    | 3 => orderedInterval (-90647982893 / 1000000000000) (-90647955331 / 1000000000000)
    | _ => orderedInterval (123564450289 / 1000000000000) (123564493654 / 1000000000000)

theorem compactCertificate512_stateChecks0 :
    compactCertificate512.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (767 / 2)) (orderedInterval (34519445285 / 1000000000000) (34519445286 / 1000000000000), orderedInterval (21598301898 / 1000000000000) (21598301899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1129937457040067 / 4000000000000)) (orderedInterval (23834148195 / 1000000000000) (23834148196 / 1000000000000), orderedInterval (41013643533 / 1000000000000) (41013643534 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (365398557576611 / 800000000000)) (orderedInterval (-33910316827 / 1000000000000) (-33910277243 / 1000000000000), orderedInterval (15654406512 / 1000000000000) (15654446096 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_stateChecks1 :
    compactCertificate512.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (329712931860169 / 4000000000000)) (orderedInterval (87811009239 / 1000000000000) (87811009255 / 1000000000000), orderedInterval (2989711666 / 1000000000000) (2989711682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (885655312936693 / 4000000000000)) (orderedInterval (40440477110 / 1000000000000) (40440555381 / 1000000000000), orderedInterval (-35302324721 / 1000000000000) (-35302246451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2404726459117281 / 4000000000000)) (orderedInterval (-30548317665 / 1000000000000) (-30548280357 / 1000000000000), orderedInterval (11239157302 / 1000000000000) (11239194610 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_stateChecks2 :
    compactCertificate512.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1771310625874153 / 4000000000000)) (orderedInterval (-22892128809 / 1000000000000) (-22892128808 / 1000000000000), orderedInterval (-30199554348 / 1000000000000) (-30199554347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3035170948457869 / 4000000000000)) (orderedInterval (-18380518988 / 1000000000000) (-18380518034 / 1000000000000), orderedInterval (22398421944 / 1000000000000) (22398422899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2235693183298471 / 4000000000000)) (orderedInterval (16327478933 / 1000000000000) (16327478934 / 1000000000000), orderedInterval (29522229412 / 1000000000000) (29522229413 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_stateChecks3 :
    compactCertificate512.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (3430128277484233 / 4000000000000)) (orderedInterval (-16759793519 / 1000000000000) (-16759793518 / 1000000000000), orderedInterval (-21472669944 / 1000000000000) (-21472669943 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1980385484360257 / 4000000000000)) (orderedInterval (-16879929021 / 1000000000000) (-16879928585 / 1000000000000), orderedInterval (31654344132 / 1000000000000) (31654344569 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 280 12 (3514228794442613 / 4000000000000)) (orderedInterval (-8044700269 / 1000000000000) (-8044700267 / 1000000000000), orderedInterval (25693145880 / 1000000000000) (25693145882 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_stateChecks4 :
    compactCertificate512.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (3283448393537897 / 4000000000000)) (orderedInterval (-27645540000 / 1000000000000) (-27645527888 / 1000000000000), orderedInterval (3374587569 / 1000000000000) (3374599681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2343223705353401 / 4000000000000)) (orderedInterval (25548454368 / 1000000000000) (25548474362 / 1000000000000), orderedInterval (-20854906342 / 1000000000000) (-20854886348 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2656965938810079 / 4000000000000)) (orderedInterval (-25898044099 / 1000000000000) (-25898007821 / 1000000000000), orderedInterval (16981441623 / 1000000000000) (16981477901 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_stateChecks5 :
    compactCertificate512.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2215101197155951 / 4000000000000)) (orderedInterval (33824191653 / 1000000000000) (33824193326 / 1000000000000), orderedInterval (-2380641267 / 1000000000000) (-2380639594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1957109084966971 / 4000000000000)) (orderedInterval (-939193068 / 1000000000000) (-939193066 / 1000000000000), orderedInterval (36060102164 / 1000000000000) (36060102165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (567246494814129 / 800000000000)) (orderedInterval (-4673179371 / 1000000000000) (-4673179369 / 1000000000000), orderedInterval (29600596580 / 1000000000000) (29600596582 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_stateChecks6 :
    compactCertificate512.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1569033657203363 / 4000000000000)) (orderedInterval (-13602287941 / 1000000000000) (-13602287940 / 1000000000000), orderedInterval (-37902826740 / 1000000000000) (-37902826739 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1330087207783243 / 4000000000000)) (orderedInterval (12847042367 / 1000000000000) (12847042368 / 1000000000000), orderedInterval (41807416614 / 1000000000000) (41807416615 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (832306816701529 / 4000000000000)) (orderedInterval (55231207368 / 1000000000000) (55231207401 / 1000000000000), orderedInterval (2875382191 / 1000000000000) (2875382223 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_stateChecks7 :
    compactCertificate512.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (447617374149543 / 4000000000000)) (orderedInterval (-29975844116 / 1000000000000) (-29975842436 / 1000000000000), orderedInterval (69347019750 / 1000000000000) (69347021430 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1215368244797629 / 4000000000000)) (orderedInterval (4908442089 / 1000000000000) (4908442096 / 1000000000000), orderedInterval (-45517883949 / 1000000000000) (-45517883942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1659481433243933 / 4000000000000)) (orderedInterval (32206905744 / 1000000000000) (32206905745 / 1000000000000), orderedInterval (22259564209 / 1000000000000) (22259564210 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_stateChecks8 :
    compactCertificate512.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (701693183298471 / 4000000000000)) (orderedInterval (16578168664 / 1000000000000) (16578168665 / 1000000000000), orderedInterval (57868428889 / 1000000000000) (57868428890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2852343833267591 / 4000000000000)) (orderedInterval (-19917715506 / 1000000000000) (-19917715505 / 1000000000000), orderedInterval (-22258255832 / 1000000000000) (-22258255831 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1905233491418569 / 4000000000000)) (orderedInterval (-15193055783 / 1000000000000) (-15193055561 / 1000000000000), orderedInterval (33268650040 / 1000000000000) (33268650262 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_states : ∀ j,
    BesselStateValid (compactCertificate512.point j) (compactCertificate512.state j) :=
  compactCertificate512.statesValid_of_checks3 compactCertificate512_stateChecks0
    compactCertificate512_stateChecks1 compactCertificate512_stateChecks2
    compactCertificate512_stateChecks3 compactCertificate512_stateChecks4
    compactCertificate512_stateChecks5 compactCertificate512_stateChecks6
    compactCertificate512_stateChecks7 compactCertificate512_stateChecks8

theorem compactCertificate512_chunkChecks0_0 :
    compactCertificate512.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (767 / 2) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34519445285 / 1000000000000) (34519445286 / 1000000000000), orderedInterval (21598301898 / 1000000000000) (21598301899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1129937457040067 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23834148195 / 1000000000000) (23834148196 / 1000000000000), orderedInterval (41013643533 / 1000000000000) (41013643534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (365398557576611 / 800000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33910316827 / 1000000000000) (-33910277243 / 1000000000000), orderedInterval (15654406512 / 1000000000000) (15654446096 / 1000000000000)))) (orderedInterval (11914491649 / 1000000000000) (11914493999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (329712931860169 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87811009239 / 1000000000000) (87811009255 / 1000000000000), orderedInterval (2989711666 / 1000000000000) (2989711682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (885655312936693 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40440477110 / 1000000000000) (40440555381 / 1000000000000), orderedInterval (-35302324721 / 1000000000000) (-35302246451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2404726459117281 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30548317665 / 1000000000000) (-30548280357 / 1000000000000), orderedInterval (11239157302 / 1000000000000) (11239194610 / 1000000000000)))) (orderedInterval (2695531496 / 1000000000000) (2695537053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1771310625874153 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22892128809 / 1000000000000) (-22892128808 / 1000000000000), orderedInterval (-30199554348 / 1000000000000) (-30199554347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3035170948457869 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18380518988 / 1000000000000) (-18380518034 / 1000000000000), orderedInterval (22398421944 / 1000000000000) (22398422899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2235693183298471 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16327478933 / 1000000000000) (16327478934 / 1000000000000), orderedInterval (29522229412 / 1000000000000) (29522229413 / 1000000000000)))) (orderedInterval (961531657 / 1000000000000) (961531709 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks0_1 :
    compactCertificate512.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3430128277484233 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16759793519 / 1000000000000) (-16759793518 / 1000000000000), orderedInterval (-21472669944 / 1000000000000) (-21472669943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1980385484360257 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16879929021 / 1000000000000) (-16879928585 / 1000000000000), orderedInterval (31654344132 / 1000000000000) (31654344569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3514228794442613 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8044700269 / 1000000000000) (-8044700267 / 1000000000000), orderedInterval (25693145880 / 1000000000000) (25693145882 / 1000000000000)))) (orderedInterval (583747496 / 1000000000000) (583747681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3283448393537897 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27645540000 / 1000000000000) (-27645527888 / 1000000000000), orderedInterval (3374587569 / 1000000000000) (3374599681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2343223705353401 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25548454368 / 1000000000000) (25548474362 / 1000000000000), orderedInterval (-20854906342 / 1000000000000) (-20854886348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2656965938810079 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25898044099 / 1000000000000) (-25898007821 / 1000000000000), orderedInterval (16981441623 / 1000000000000) (16981477901 / 1000000000000)))) (orderedInterval (3046080973 / 1000000000000) (3046083312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2215101197155951 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33824191653 / 1000000000000) (33824193326 / 1000000000000), orderedInterval (-2380641267 / 1000000000000) (-2380639594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1957109084966971 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-939193068 / 1000000000000) (-939193066 / 1000000000000), orderedInterval (36060102164 / 1000000000000) (36060102165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (567246494814129 / 800000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4673179371 / 1000000000000) (-4673179369 / 1000000000000), orderedInterval (29600596580 / 1000000000000) (29600596582 / 1000000000000)))) (orderedInterval (324685632 / 1000000000000) (324685689 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks0_2 :
    compactCertificate512.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1569033657203363 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13602287941 / 1000000000000) (-13602287940 / 1000000000000), orderedInterval (-37902826740 / 1000000000000) (-37902826739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1330087207783243 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12847042367 / 1000000000000) (12847042368 / 1000000000000), orderedInterval (41807416614 / 1000000000000) (41807416615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (832306816701529 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (55231207368 / 1000000000000) (55231207401 / 1000000000000), orderedInterval (2875382191 / 1000000000000) (2875382223 / 1000000000000)))) (orderedInterval (3245827878 / 1000000000000) (3245827976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (447617374149543 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29975844116 / 1000000000000) (-29975842436 / 1000000000000), orderedInterval (69347019750 / 1000000000000) (69347021430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1215368244797629 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4908442089 / 1000000000000) (4908442096 / 1000000000000), orderedInterval (-45517883949 / 1000000000000) (-45517883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1659481433243933 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32206905744 / 1000000000000) (32206905745 / 1000000000000), orderedInterval (22259564209 / 1000000000000) (22259564210 / 1000000000000)))) (orderedInterval (-2026150596 / 1000000000000) (-2026150519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (701693183298471 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16578168664 / 1000000000000) (16578168665 / 1000000000000), orderedInterval (57868428889 / 1000000000000) (57868428890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2852343833267591 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19917715506 / 1000000000000) (-19917715505 / 1000000000000), orderedInterval (-22258255832 / 1000000000000) (-22258255831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1905233491418569 / 4000000000000) 0 (IntervalRat.scale (767 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15193055783 / 1000000000000) (-15193055561 / 1000000000000), orderedInterval (33268650040 / 1000000000000) (33268650262 / 1000000000000)))) (orderedInterval (4571896270 / 1000000000000) (4571896419 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks0 :
    compactCertificate512.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate512.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate512_chunkChecks0_0
    compactCertificate512_chunkChecks0_1 compactCertificate512_chunkChecks0_2

theorem compactCertificate512_chunkChecks1_0 :
    compactCertificate512.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (767 / 2) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34519445285 / 1000000000000) (34519445286 / 1000000000000), orderedInterval (21598301898 / 1000000000000) (21598301899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1129937457040067 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23834148195 / 1000000000000) (23834148196 / 1000000000000), orderedInterval (41013643533 / 1000000000000) (41013643534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (365398557576611 / 800000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33910316827 / 1000000000000) (-33910277243 / 1000000000000), orderedInterval (15654406512 / 1000000000000) (15654446096 / 1000000000000)))) (orderedInterval (9936387496 / 1000000000000) (9936390293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (329712931860169 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87811009239 / 1000000000000) (87811009255 / 1000000000000), orderedInterval (2989711666 / 1000000000000) (2989711682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (885655312936693 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40440477110 / 1000000000000) (40440555381 / 1000000000000), orderedInterval (-35302324721 / 1000000000000) (-35302246451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2404726459117281 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30548317665 / 1000000000000) (-30548280357 / 1000000000000), orderedInterval (11239157302 / 1000000000000) (11239194610 / 1000000000000)))) (orderedInterval (-2003658941 / 1000000000000) (-2003653081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1771310625874153 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22892128809 / 1000000000000) (-22892128808 / 1000000000000), orderedInterval (-30199554348 / 1000000000000) (-30199554347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3035170948457869 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18380518988 / 1000000000000) (-18380518034 / 1000000000000), orderedInterval (22398421944 / 1000000000000) (22398422899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2235693183298471 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16327478933 / 1000000000000) (16327478934 / 1000000000000), orderedInterval (29522229412 / 1000000000000) (29522229413 / 1000000000000)))) (orderedInterval (-327063431 / 1000000000000) (-327063335 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks1_1 :
    compactCertificate512.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3430128277484233 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16759793519 / 1000000000000) (-16759793518 / 1000000000000), orderedInterval (-21472669944 / 1000000000000) (-21472669943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1980385484360257 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16879929021 / 1000000000000) (-16879928585 / 1000000000000), orderedInterval (31654344132 / 1000000000000) (31654344569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3514228794442613 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8044700269 / 1000000000000) (-8044700267 / 1000000000000), orderedInterval (25693145880 / 1000000000000) (25693145882 / 1000000000000)))) (orderedInterval (19926701957 / 1000000000000) (19926702315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3283448393537897 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27645540000 / 1000000000000) (-27645527888 / 1000000000000), orderedInterval (3374587569 / 1000000000000) (3374599681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2343223705353401 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25548454368 / 1000000000000) (25548474362 / 1000000000000), orderedInterval (-20854906342 / 1000000000000) (-20854886348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2656965938810079 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25898044099 / 1000000000000) (-25898007821 / 1000000000000), orderedInterval (16981441623 / 1000000000000) (16981477901 / 1000000000000)))) (orderedInterval (-3291678018 / 1000000000000) (-3291674269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2215101197155951 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33824191653 / 1000000000000) (33824193326 / 1000000000000), orderedInterval (-2380641267 / 1000000000000) (-2380639594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1957109084966971 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-939193068 / 1000000000000) (-939193066 / 1000000000000), orderedInterval (36060102164 / 1000000000000) (36060102165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (567246494814129 / 800000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4673179371 / 1000000000000) (-4673179369 / 1000000000000), orderedInterval (29600596580 / 1000000000000) (29600596582 / 1000000000000)))) (orderedInterval (-1271203766 / 1000000000000) (-1271203684 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks1_2 :
    compactCertificate512.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1569033657203363 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13602287941 / 1000000000000) (-13602287940 / 1000000000000), orderedInterval (-37902826740 / 1000000000000) (-37902826739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1330087207783243 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12847042367 / 1000000000000) (12847042368 / 1000000000000), orderedInterval (41807416614 / 1000000000000) (41807416615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (832306816701529 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (55231207368 / 1000000000000) (55231207401 / 1000000000000), orderedInterval (2875382191 / 1000000000000) (2875382223 / 1000000000000)))) (orderedInterval (4197823838 / 1000000000000) (4197823928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (447617374149543 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29975844116 / 1000000000000) (-29975842436 / 1000000000000), orderedInterval (69347019750 / 1000000000000) (69347021430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1215368244797629 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4908442089 / 1000000000000) (4908442096 / 1000000000000), orderedInterval (-45517883949 / 1000000000000) (-45517883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1659481433243933 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32206905744 / 1000000000000) (32206905745 / 1000000000000), orderedInterval (22259564209 / 1000000000000) (22259564210 / 1000000000000)))) (orderedInterval (-1400980159 / 1000000000000) (-1400980108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (701693183298471 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16578168664 / 1000000000000) (16578168665 / 1000000000000), orderedInterval (57868428889 / 1000000000000) (57868428890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2852343833267591 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19917715506 / 1000000000000) (-19917715505 / 1000000000000), orderedInterval (-22258255832 / 1000000000000) (-22258255831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1905233491418569 / 4000000000000) 1 (IntervalRat.scale (767 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15193055783 / 1000000000000) (-15193055561 / 1000000000000), orderedInterval (33268650040 / 1000000000000) (33268650262 / 1000000000000)))) (orderedInterval (-4224109976 / 1000000000000) (-4224109774 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks1 :
    compactCertificate512.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate512.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate512_chunkChecks1_0
    compactCertificate512_chunkChecks1_1 compactCertificate512_chunkChecks1_2

theorem compactCertificate512_chunkChecks2_0 :
    compactCertificate512.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (767 / 2) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34519445285 / 1000000000000) (34519445286 / 1000000000000), orderedInterval (21598301898 / 1000000000000) (21598301899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1129937457040067 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23834148195 / 1000000000000) (23834148196 / 1000000000000), orderedInterval (41013643533 / 1000000000000) (41013643534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (365398557576611 / 800000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33910316827 / 1000000000000) (-33910277243 / 1000000000000), orderedInterval (15654406512 / 1000000000000) (15654446096 / 1000000000000)))) (orderedInterval (-11006085703 / 1000000000000) (-11006082366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (329712931860169 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87811009239 / 1000000000000) (87811009255 / 1000000000000), orderedInterval (2989711666 / 1000000000000) (2989711682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (885655312936693 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40440477110 / 1000000000000) (40440555381 / 1000000000000), orderedInterval (-35302324721 / 1000000000000) (-35302246451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2404726459117281 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30548317665 / 1000000000000) (-30548280357 / 1000000000000), orderedInterval (11239157302 / 1000000000000) (11239194610 / 1000000000000)))) (orderedInterval (-5779666547 / 1000000000000) (-5779658989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1771310625874153 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22892128809 / 1000000000000) (-22892128808 / 1000000000000), orderedInterval (-30199554348 / 1000000000000) (-30199554347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3035170948457869 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18380518988 / 1000000000000) (-18380518034 / 1000000000000), orderedInterval (22398421944 / 1000000000000) (22398422899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2235693183298471 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16327478933 / 1000000000000) (16327478934 / 1000000000000), orderedInterval (29522229412 / 1000000000000) (29522229413 / 1000000000000)))) (orderedInterval (-3056764260 / 1000000000000) (-3056764078 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks2_1 :
    compactCertificate512.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3430128277484233 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16759793519 / 1000000000000) (-16759793518 / 1000000000000), orderedInterval (-21472669944 / 1000000000000) (-21472669943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1980385484360257 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16879929021 / 1000000000000) (-16879928585 / 1000000000000), orderedInterval (31654344132 / 1000000000000) (31654344569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3514228794442613 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8044700269 / 1000000000000) (-8044700267 / 1000000000000), orderedInterval (25693145880 / 1000000000000) (25693145882 / 1000000000000)))) (orderedInterval (-6855750153 / 1000000000000) (-6855749422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3283448393537897 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27645540000 / 1000000000000) (-27645527888 / 1000000000000), orderedInterval (3374587569 / 1000000000000) (3374599681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2343223705353401 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25548454368 / 1000000000000) (25548474362 / 1000000000000), orderedInterval (-20854906342 / 1000000000000) (-20854886348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2656965938810079 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25898044099 / 1000000000000) (-25898007821 / 1000000000000), orderedInterval (16981441623 / 1000000000000) (16981477901 / 1000000000000)))) (orderedInterval (-8308359051 / 1000000000000) (-8308352954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2215101197155951 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33824191653 / 1000000000000) (33824193326 / 1000000000000), orderedInterval (-2380641267 / 1000000000000) (-2380639594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1957109084966971 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-939193068 / 1000000000000) (-939193066 / 1000000000000), orderedInterval (36060102164 / 1000000000000) (36060102165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (567246494814129 / 800000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4673179371 / 1000000000000) (-4673179369 / 1000000000000), orderedInterval (29600596580 / 1000000000000) (29600596582 / 1000000000000)))) (orderedInterval (-489581164 / 1000000000000) (-489581044 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks2_2 :
    compactCertificate512.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1569033657203363 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13602287941 / 1000000000000) (-13602287940 / 1000000000000), orderedInterval (-37902826740 / 1000000000000) (-37902826739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1330087207783243 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12847042367 / 1000000000000) (12847042368 / 1000000000000), orderedInterval (41807416614 / 1000000000000) (41807416615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (832306816701529 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (55231207368 / 1000000000000) (55231207401 / 1000000000000), orderedInterval (2875382191 / 1000000000000) (2875382223 / 1000000000000)))) (orderedInterval (-2268975003 / 1000000000000) (-2268974917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (447617374149543 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29975844116 / 1000000000000) (-29975842436 / 1000000000000), orderedInterval (69347019750 / 1000000000000) (69347021430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1215368244797629 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4908442089 / 1000000000000) (4908442096 / 1000000000000), orderedInterval (-45517883949 / 1000000000000) (-45517883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1659481433243933 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32206905744 / 1000000000000) (32206905745 / 1000000000000), orderedInterval (22259564209 / 1000000000000) (22259564210 / 1000000000000)))) (orderedInterval (2915056945 / 1000000000000) (2915056989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (701693183298471 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16578168664 / 1000000000000) (16578168665 / 1000000000000), orderedInterval (57868428889 / 1000000000000) (57868428890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2852343833267591 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19917715506 / 1000000000000) (-19917715505 / 1000000000000), orderedInterval (-22258255832 / 1000000000000) (-22258255831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1905233491418569 / 4000000000000) 2 (IntervalRat.scale (767 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15193055783 / 1000000000000) (-15193055561 / 1000000000000), orderedInterval (33268650040 / 1000000000000) (33268650262 / 1000000000000)))) (orderedInterval (-10012842188 / 1000000000000) (-10012841903 / 1000000000000))) = true
  rfl'

theorem compactCertificate512_chunkChecks2 :
    compactCertificate512.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate512.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate512_chunkChecks2_0
    compactCertificate512_chunkChecks2_1 compactCertificate512_chunkChecks2_2

theorem compactCertificate512_chunkChecks3_0 :
    compactCertificate512.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (767 / 2) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34519445285 / 1000000000000) (34519445286 / 1000000000000), orderedInterval (21598301898 / 1000000000000) (21598301899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1129937457040067 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23834148195 / 1000000000000) (23834148196 / 1000000000000), orderedInterval (41013643533 / 1000000000000) (41013643534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (365398557576611 / 800000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33910316827 / 1000000000000) (-33910277243 / 1000000000000), orderedInterval (15654406512 / 1000000000000) (15654446096 / 1000000000000)))) (orderedInterval (-10236704832 / 1000000000000) (-10236700858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (329712931860169 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87811009239 / 1000000000000) (87811009255 / 1000000000000), orderedInterval (2989711666 / 1000000000000) (2989711682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (885655312936693 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40440477110 / 1000000000000) (40440555381 / 1000000000000), orderedInterval (-35302324721 / 1000000000000) (-35302246451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2404726459117281 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30548317665 / 1000000000000) (-30548280357 / 1000000000000), orderedInterval (11239157302 / 1000000000000) (11239194610 / 1000000000000)))) (orderedInterval (3341383413 / 1000000000000) (3341394308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1771310625874153 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22892128809 / 1000000000000) (-22892128808 / 1000000000000), orderedInterval (-30199554348 / 1000000000000) (-30199554347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3035170948457869 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18380518988 / 1000000000000) (-18380518034 / 1000000000000), orderedInterval (22398421944 / 1000000000000) (22398422899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2235693183298471 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16327478933 / 1000000000000) (16327478934 / 1000000000000), orderedInterval (29522229412 / 1000000000000) (29522229413 / 1000000000000)))) (orderedInterval (3150523860 / 1000000000000) (3150524210 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate512_chunkChecks3_1 :
    compactCertificate512.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3430128277484233 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16759793519 / 1000000000000) (-16759793518 / 1000000000000), orderedInterval (-21472669944 / 1000000000000) (-21472669943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1980385484360257 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16879929021 / 1000000000000) (-16879928585 / 1000000000000), orderedInterval (31654344132 / 1000000000000) (31654344569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3514228794442613 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8044700269 / 1000000000000) (-8044700267 / 1000000000000), orderedInterval (25693145880 / 1000000000000) (25693145882 / 1000000000000)))) (orderedInterval (-91599487914 / 1000000000000) (-91599486359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3283448393537897 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27645540000 / 1000000000000) (-27645527888 / 1000000000000), orderedInterval (3374587569 / 1000000000000) (3374599681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2343223705353401 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25548454368 / 1000000000000) (25548474362 / 1000000000000), orderedInterval (-20854906342 / 1000000000000) (-20854886348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2656965938810079 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25898044099 / 1000000000000) (-25898007821 / 1000000000000), orderedInterval (16981441623 / 1000000000000) (16981477901 / 1000000000000)))) (orderedInterval (8094608893 / 1000000000000) (8094618954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2215101197155951 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33824191653 / 1000000000000) (33824193326 / 1000000000000), orderedInterval (-2380641267 / 1000000000000) (-2380639594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1957109084966971 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-939193068 / 1000000000000) (-939193066 / 1000000000000), orderedInterval (36060102164 / 1000000000000) (36060102165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (567246494814129 / 800000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4673179371 / 1000000000000) (-4673179369 / 1000000000000), orderedInterval (29600596580 / 1000000000000) (29600596582 / 1000000000000)))) (orderedInterval (-420762524 / 1000000000000) (-420762344 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate512_chunkChecks3_2 :
    compactCertificate512.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1569033657203363 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13602287941 / 1000000000000) (-13602287940 / 1000000000000), orderedInterval (-37902826740 / 1000000000000) (-37902826739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1330087207783243 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12847042367 / 1000000000000) (12847042368 / 1000000000000), orderedInterval (41807416614 / 1000000000000) (41807416615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (832306816701529 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (55231207368 / 1000000000000) (55231207401 / 1000000000000), orderedInterval (2875382191 / 1000000000000) (2875382223 / 1000000000000)))) (orderedInterval (-4951629591 / 1000000000000) (-4951629508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (447617374149543 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29975844116 / 1000000000000) (-29975842436 / 1000000000000), orderedInterval (69347019750 / 1000000000000) (69347021430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1215368244797629 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4908442089 / 1000000000000) (4908442096 / 1000000000000), orderedInterval (-45517883949 / 1000000000000) (-45517883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1659481433243933 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32206905744 / 1000000000000) (32206905745 / 1000000000000), orderedInterval (22259564209 / 1000000000000) (22259564210 / 1000000000000)))) (orderedInterval (1670395313 / 1000000000000) (1670395356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (701693183298471 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16578168664 / 1000000000000) (16578168665 / 1000000000000), orderedInterval (57868428889 / 1000000000000) (57868428890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2852343833267591 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19917715506 / 1000000000000) (-19917715505 / 1000000000000), orderedInterval (-22258255832 / 1000000000000) (-22258255831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1905233491418569 / 4000000000000) 3 (IntervalRat.scale (767 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15193055783 / 1000000000000) (-15193055561 / 1000000000000), orderedInterval (33268650040 / 1000000000000) (33268650262 / 1000000000000)))) (orderedInterval (303690489 / 1000000000000) (303690910 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate512_chunkChecks3 :
    compactCertificate512.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate512.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate512_chunkChecks3_0
    compactCertificate512_chunkChecks3_1 compactCertificate512_chunkChecks3_2

theorem compactCertificate512_chunkChecks4_0 :
    compactCertificate512.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (767 / 2) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34519445285 / 1000000000000) (34519445286 / 1000000000000), orderedInterval (21598301898 / 1000000000000) (21598301899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1129937457040067 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23834148195 / 1000000000000) (23834148196 / 1000000000000), orderedInterval (41013643533 / 1000000000000) (41013643534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (365398557576611 / 800000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33910316827 / 1000000000000) (-33910277243 / 1000000000000), orderedInterval (15654406512 / 1000000000000) (15654446096 / 1000000000000)))) (orderedInterval (9797153749 / 1000000000000) (9797158491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (329712931860169 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (87811009239 / 1000000000000) (87811009255 / 1000000000000), orderedInterval (2989711666 / 1000000000000) (2989711682 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (885655312936693 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40440477110 / 1000000000000) (40440555381 / 1000000000000), orderedInterval (-35302324721 / 1000000000000) (-35302246451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2404726459117281 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30548317665 / 1000000000000) (-30548280357 / 1000000000000), orderedInterval (11239157302 / 1000000000000) (11239194610 / 1000000000000)))) (orderedInterval (13259142729 / 1000000000000) (13259159287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1771310625874153 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22892128809 / 1000000000000) (-22892128808 / 1000000000000), orderedInterval (-30199554348 / 1000000000000) (-30199554347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3035170948457869 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18380518988 / 1000000000000) (-18380518034 / 1000000000000), orderedInterval (22398421944 / 1000000000000) (22398422899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2235693183298471 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16327478933 / 1000000000000) (16327478934 / 1000000000000), orderedInterval (29522229412 / 1000000000000) (29522229413 / 1000000000000)))) (orderedInterval (10452705083 / 1000000000000) (10452705759 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate512_chunkChecks4_1 :
    compactCertificate512.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3430128277484233 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16759793519 / 1000000000000) (-16759793518 / 1000000000000), orderedInterval (-21472669944 / 1000000000000) (-21472669943 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1980385484360257 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16879929021 / 1000000000000) (-16879928585 / 1000000000000), orderedInterval (31654344132 / 1000000000000) (31654344569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3514228794442613 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8044700269 / 1000000000000) (-8044700267 / 1000000000000), orderedInterval (25693145880 / 1000000000000) (25693145882 / 1000000000000)))) (orderedInterval (39955153915 / 1000000000000) (39955157303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3283448393537897 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27645540000 / 1000000000000) (-27645527888 / 1000000000000), orderedInterval (3374587569 / 1000000000000) (3374599681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2343223705353401 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (25548454368 / 1000000000000) (25548474362 / 1000000000000), orderedInterval (-20854906342 / 1000000000000) (-20854886348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2656965938810079 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25898044099 / 1000000000000) (-25898007821 / 1000000000000), orderedInterval (16981441623 / 1000000000000) (16981477901 / 1000000000000)))) (orderedInterval (24766687294 / 1000000000000) (24766704243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2215101197155951 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33824191653 / 1000000000000) (33824193326 / 1000000000000), orderedInterval (-2380641267 / 1000000000000) (-2380639594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1957109084966971 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-939193068 / 1000000000000) (-939193066 / 1000000000000), orderedInterval (36060102164 / 1000000000000) (36060102165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (567246494814129 / 800000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4673179371 / 1000000000000) (-4673179369 / 1000000000000), orderedInterval (29600596580 / 1000000000000) (29600596582 / 1000000000000)))) (orderedInterval (444562841 / 1000000000000) (444563119 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate512_chunkChecks4_2 :
    compactCertificate512.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1569033657203363 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13602287941 / 1000000000000) (-13602287940 / 1000000000000), orderedInterval (-37902826740 / 1000000000000) (-37902826739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1330087207783243 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12847042367 / 1000000000000) (12847042368 / 1000000000000), orderedInterval (41807416614 / 1000000000000) (41807416615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (832306816701529 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (55231207368 / 1000000000000) (55231207401 / 1000000000000), orderedInterval (2875382191 / 1000000000000) (2875382223 / 1000000000000)))) (orderedInterval (2151132801 / 1000000000000) (2151132883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (447617374149543 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29975844116 / 1000000000000) (-29975842436 / 1000000000000), orderedInterval (69347019750 / 1000000000000) (69347021430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1215368244797629 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4908442089 / 1000000000000) (4908442096 / 1000000000000), orderedInterval (-45517883949 / 1000000000000) (-45517883942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1659481433243933 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32206905744 / 1000000000000) (32206905745 / 1000000000000), orderedInterval (22259564209 / 1000000000000) (22259564210 / 1000000000000)))) (orderedInterval (-3429098126 / 1000000000000) (-3429098080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (701693183298471 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16578168664 / 1000000000000) (16578168665 / 1000000000000), orderedInterval (57868428889 / 1000000000000) (57868428890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2852343833267591 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19917715506 / 1000000000000) (-19917715505 / 1000000000000), orderedInterval (-22258255832 / 1000000000000) (-22258255831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1905233491418569 / 4000000000000) 4 (IntervalRat.scale (767 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15193055783 / 1000000000000) (-15193055561 / 1000000000000), orderedInterval (33268650040 / 1000000000000) (33268650262 / 1000000000000)))) (orderedInterval (26167010003 / 1000000000000) (26167010649 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate512_chunkChecks4 :
    compactCertificate512.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate512.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate512_chunkChecks4_0
    compactCertificate512_chunkChecks4_1 compactCertificate512_chunkChecks4_2

theorem compactCertificate512_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate512.chunkCheck r b = true :=
  compactCertificate512.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate512_chunkChecks0
    · exact compactCertificate512_chunkChecks1
    · exact compactCertificate512_chunkChecks2
    · exact compactCertificate512_chunkChecks3
    · exact compactCertificate512_chunkChecks4)

theorem compactCertificate512_coefficient0 :
    compactCertificate512.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate512_coefficient1 :
    compactCertificate512.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate512_coefficient2 :
    compactCertificate512.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate512_coefficient3 :
    compactCertificate512.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate512_coefficient4 :
    compactCertificate512.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate512_coefficients : ∀ r : Fin 5,
    compactCertificate512.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate512_coefficient0
  · exact compactCertificate512_coefficient1
  · exact compactCertificate512_coefficient2
  · exact compactCertificate512_coefficient3
  · exact compactCertificate512_coefficient4

theorem compactCertificate512_lower : (1 : ℚ) ≤ compactCertificate512.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate512, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate512_proves {t : ℝ} (ht : t ∈ compactCertificate512.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate512.proves compactCertificate512_states compactCertificate512_chunks
    compactCertificate512_coefficients compactCertificate512_lower ht

end Erdos232
