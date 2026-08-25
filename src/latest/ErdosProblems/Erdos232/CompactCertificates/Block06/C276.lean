/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate276 : CompactCertificate where
  left := 150
  right := 151
  center := 301 / 2
  grid := fun i =>
    match i.val with
    | 0 => 48
    | 1 => 35
    | 2 => 57
    | 3 => 10
    | 4 => 28
    | 5 => 75
    | 6 => 55
    | 7 => 95
    | 8 => 70
    | 9 => 107
    | 10 => 62
    | 11 => 110
    | 12 => 103
    | 13 => 73
    | 14 => 83
    | 15 => 69
    | 16 => 61
    | 17 => 89
    | 18 => 49
    | 19 => 42
    | 20 => 26
    | 21 => 14
    | 22 => 38
    | 23 => 52
    | 24 => 22
    | 25 => 89
    | _ => 60
  point := fun i =>
    match i.val with
    | 0 => 301 / 2
    | 1 => 443430475318201 / 4000000000000
    | 2 => 143396304863833 / 800000000000
    | 3 => 129391906766507 / 4000000000000
    | 4 => 347564862052079 / 4000000000000
    | 5 => 943706211465843 / 4000000000000
    | 6 => 695129724104459 / 4000000000000
    | 7 => 1191116630359607 / 4000000000000
    | 8 => 877371118869413 / 4000000000000
    | 9 => 1346112922454699 / 4000000000000
    | 10 => 777178658138771 / 4000000000000
    | 11 => 1379117167049839 / 4000000000000
    | 12 => 1288550151831691 / 4000000000000
    | 13 => 919570189454203 / 4000000000000
    | 14 => 1042694586156237 / 4000000000000
    | 15 => 869290039561853 / 4000000000000
    | 16 => 768044112874913 / 4000000000000
    | 17 => 222609119868387 / 800000000000
    | 18 => 615748540832089 / 4000000000000
    | 19 => 521976857291729 / 4000000000000
    | 20 => 326628881130587 / 4000000000000
    | 21 => 175662098590629 / 4000000000000
    | 22 => 476956768818887 / 4000000000000
    | 23 => 651243691533799 / 4000000000000
    | 24 => 275371118869413 / 4000000000000
    | 25 => 1119368310056773 / 4000000000000
    | _ => 747686155041707 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (30500883754 / 1000000000000) (30500883755 / 1000000000000), orderedInterval (57342040310 / 1000000000000) (57342040311 / 1000000000000))
    | 1 => (orderedInterval (-75276489547 / 1000000000000) (-75276489363 / 1000000000000), orderedInterval (9061481447 / 1000000000000) (9061481631 / 1000000000000))
    | 2 => (orderedInterval (-48796413322 / 1000000000000) (-48796413321 / 1000000000000), orderedInterval (-34077501969 / 1000000000000) (-34077501968 / 1000000000000))
    | 3 => (orderedInterval (138850702533 / 1000000000000) (138850702694 / 1000000000000), orderedInterval (-22110375813 / 1000000000000) (-22110375652 / 1000000000000))
    | 4 => (orderedInterval (-24428438873 / 1000000000000) (-24428438408 / 1000000000000), orderedInterval (82177036230 / 1000000000000) (82177036695 / 1000000000000))
    | 5 => (orderedInterval (-46103911818 / 1000000000000) (-46103911817 / 1000000000000), orderedInterval (-23835679343 / 1000000000000) (-23835679342 / 1000000000000))
    | 6 => (orderedInterval (-59211647519 / 1000000000000) (-59211646619 / 1000000000000), orderedInterval (12711567989 / 1000000000000) (12711568889 / 1000000000000))
    | 7 => (orderedInterval (-5206072872 / 1000000000000) (-5206072871 / 1000000000000), orderedInterval (-45934615573 / 1000000000000) (-45934615572 / 1000000000000))
    | 8 => (orderedInterval (11552903122 / 1000000000000) (11552903123 / 1000000000000), orderedInterval (52594326518 / 1000000000000) (52594326519 / 1000000000000))
    | 9 => (orderedInterval (-39924634207 / 1000000000000) (-39924634206 / 1000000000000), orderedInterval (-17196111104 / 1000000000000) (-17196111103 / 1000000000000))
    | 10 => (orderedInterval (16952837152 / 1000000000000) (16952837153 / 1000000000000), orderedInterval (54629755969 / 1000000000000) (54629755970 / 1000000000000))
    | 11 => (orderedInterval (-466843349 / 1000000000000) (-466843347 / 1000000000000), orderedInterval (42968571328 / 1000000000000) (42968571329 / 1000000000000))
    | 12 => (orderedInterval (27308492855 / 1000000000000) (27308501009 / 1000000000000), orderedInterval (-35120624077 / 1000000000000) (-35120615923 / 1000000000000))
    | 13 => (orderedInterval (-51241520561 / 1000000000000) (-51241520559 / 1000000000000), orderedInterval (-11867973134 / 1000000000000) (-11867973131 / 1000000000000))
    | 14 => (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))
    | 15 => (orderedInterval (-52656672577 / 1000000000000) (-52656672574 / 1000000000000), orderedInterval (-12394677033 / 1000000000000) (-12394677031 / 1000000000000))
    | 16 => (orderedInterval (-52758378368 / 1000000000000) (-52758378367 / 1000000000000), orderedInterval (-22929550696 / 1000000000000) (-22929550695 / 1000000000000))
    | 17 => (orderedInterval (25220594374 / 1000000000000) (25220597760 / 1000000000000), orderedInterval (-40687306798 / 1000000000000) (-40687303413 / 1000000000000))
    | 18 => (orderedInterval (-45394718923 / 1000000000000) (-45394718922 / 1000000000000), orderedInterval (-45403652423 / 1000000000000) (-45403652422 / 1000000000000))
    | 19 => (orderedInterval (-43276932122 / 1000000000000) (-43276909795 / 1000000000000), orderedInterval (54989569188 / 1000000000000) (54989591515 / 1000000000000))
    | 20 => (orderedInterval (60808120081 / 1000000000000) (60808120082 / 1000000000000), orderedInterval (63648188528 / 1000000000000) (63648188529 / 1000000000000))
    | 21 => (orderedInterval (79005497300 / 1000000000000) (79005497301 / 1000000000000), orderedInterval (89956114583 / 1000000000000) (89956114584 / 1000000000000))
    | 22 => (orderedInterval (43812888752 / 1000000000000) (43812888753 / 1000000000000), orderedInterval (58292420318 / 1000000000000) (58292420319 / 1000000000000))
    | 23 => (orderedInterval (14422209639 / 1000000000000) (14422209640 / 1000000000000), orderedInterval (60801373389 / 1000000000000) (60801373390 / 1000000000000))
    | 24 => (orderedInterval (47055351978 / 1000000000000) (47055351979 / 1000000000000), orderedInterval (83523419491 / 1000000000000) (83523419492 / 1000000000000))
    | 25 => (orderedInterval (-40773566108 / 1000000000000) (-40773566107 / 1000000000000), orderedInterval (-24674669342 / 1000000000000) (-24674669341 / 1000000000000))
    | _ => (orderedInterval (-41426567453 / 1000000000000) (-41426515658 / 1000000000000), orderedInterval (41216189543 / 1000000000000) (41216241338 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8524622562 / 1000000000000) (8524622576 / 1000000000000)
      | 1 => orderedInterval (879153896 / 1000000000000) (879153934 / 1000000000000)
      | 2 => orderedInterval (439786987 / 1000000000000) (439786996 / 1000000000000)
      | 3 => orderedInterval (8283826614 / 1000000000000) (8283826674 / 1000000000000)
      | 4 => orderedInterval (-5176221229 / 1000000000000) (-5176221063 / 1000000000000)
      | 5 => orderedInterval (3056871629 / 1000000000000) (3056871731 / 1000000000000)
      | 6 => orderedInterval (11687368462 / 1000000000000) (11687369764 / 1000000000000)
      | 7 => orderedInterval (-3558124571 / 1000000000000) (-3558124552 / 1000000000000)
      | _ => orderedInterval (11375419069 / 1000000000000) (11375428830 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (20408923097 / 1000000000000) (20408923111 / 1000000000000)
      | 1 => orderedInterval (4440138787 / 1000000000000) (4440138819 / 1000000000000)
      | 2 => orderedInterval (4655830837 / 1000000000000) (4655830852 / 1000000000000)
      | 3 => orderedInterval (26051156897 / 1000000000000) (26051157022 / 1000000000000)
      | 4 => orderedInterval (-28197330 / 1000000000000) (-28196984 / 1000000000000)
      | 5 => orderedInterval (-458686375 / 1000000000000) (-458686193 / 1000000000000)
      | 6 => orderedInterval (5851075585 / 1000000000000) (5851076716 / 1000000000000)
      | 7 => orderedInterval (-6573384437 / 1000000000000) (-6573384420 / 1000000000000)
      | _ => orderedInterval (-5639667566 / 1000000000000) (-5639655436 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-7782798213 / 1000000000000) (-7782798197 / 1000000000000)
      | 1 => orderedInterval (-7716843711 / 1000000000000) (-7716843675 / 1000000000000)
      | 2 => orderedInterval (-1252637935 / 1000000000000) (-1252637908 / 1000000000000)
      | 3 => orderedInterval (-37388874132 / 1000000000000) (-37388873863 / 1000000000000)
      | 4 => orderedInterval (13078181046 / 1000000000000) (13078181772 / 1000000000000)
      | 5 => orderedInterval (-5850913524 / 1000000000000) (-5850913195 / 1000000000000)
      | 6 => orderedInterval (-10056782670 / 1000000000000) (-10056781678 / 1000000000000)
      | 7 => orderedInterval (2085354869 / 1000000000000) (2085354886 / 1000000000000)
      | _ => orderedInterval (-23487214384 / 1000000000000) (-23487199225 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19331189159 / 1000000000000) (-19331189141 / 1000000000000)
      | 1 => orderedInterval (-7055963045 / 1000000000000) (-7055962998 / 1000000000000)
      | 2 => orderedInterval (-14900919962 / 1000000000000) (-14900919914 / 1000000000000)
      | 3 => orderedInterval (-116061005925 / 1000000000000) (-116061005340 / 1000000000000)
      | 4 => orderedInterval (-3291486783 / 1000000000000) (-3291485251 / 1000000000000)
      | 5 => orderedInterval (4329220797 / 1000000000000) (4329221396 / 1000000000000)
      | 6 => orderedInterval (-6003524065 / 1000000000000) (-6003523202 / 1000000000000)
      | 7 => orderedInterval (6584174706 / 1000000000000) (6584174724 / 1000000000000)
      | _ => orderedInterval (2010976584 / 1000000000000) (2010995436 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (6378077730 / 1000000000000) (6378077750 / 1000000000000)
      | 1 => orderedInterval (19783822751 / 1000000000000) (19783822820 / 1000000000000)
      | 2 => orderedInterval (3918701601 / 1000000000000) (3918701690 / 1000000000000)
      | 3 => orderedInterval (180554977945 / 1000000000000) (180554979247 / 1000000000000)
      | 4 => orderedInterval (-35224335422 / 1000000000000) (-35224332169 / 1000000000000)
      | 5 => orderedInterval (12843895101 / 1000000000000) (12843896199 / 1000000000000)
      | 6 => orderedInterval (9579785598 / 1000000000000) (9579786356 / 1000000000000)
      | 7 => orderedInterval (-2003439085 / 1000000000000) (-2003439066 / 1000000000000)
      | _ => orderedInterval (58155229217 / 1000000000000) (58155252802 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (35512703419 / 1000000000000) (35512714890 / 1000000000000)
    | 1 => orderedInterval (48707189495 / 1000000000000) (48707203487 / 1000000000000)
    | 2 => orderedInterval (-78372528654 / 1000000000000) (-78372511083 / 1000000000000)
    | 3 => orderedInterval (-153719716852 / 1000000000000) (-153719694290 / 1000000000000)
    | _ => orderedInterval (253986715436 / 1000000000000) (253986745629 / 1000000000000)

theorem compactCertificate276_stateChecks0 :
    compactCertificate276.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (301 / 2)) (orderedInterval (30500883754 / 1000000000000) (30500883755 / 1000000000000), orderedInterval (57342040310 / 1000000000000) (57342040311 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (443430475318201 / 4000000000000)) (orderedInterval (-75276489547 / 1000000000000) (-75276489363 / 1000000000000), orderedInterval (9061481447 / 1000000000000) (9061481631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (143396304863833 / 800000000000)) (orderedInterval (-48796413322 / 1000000000000) (-48796413321 / 1000000000000), orderedInterval (-34077501969 / 1000000000000) (-34077501968 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_stateChecks1 :
    compactCertificate276.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (129391906766507 / 4000000000000)) (orderedInterval (138850702533 / 1000000000000) (138850702694 / 1000000000000), orderedInterval (-22110375813 / 1000000000000) (-22110375652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (347564862052079 / 4000000000000)) (orderedInterval (-24428438873 / 1000000000000) (-24428438408 / 1000000000000), orderedInterval (82177036230 / 1000000000000) (82177036695 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (943706211465843 / 4000000000000)) (orderedInterval (-46103911818 / 1000000000000) (-46103911817 / 1000000000000), orderedInterval (-23835679343 / 1000000000000) (-23835679342 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_stateChecks2 :
    compactCertificate276.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (695129724104459 / 4000000000000)) (orderedInterval (-59211647519 / 1000000000000) (-59211646619 / 1000000000000), orderedInterval (12711567989 / 1000000000000) (12711568889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1191116630359607 / 4000000000000)) (orderedInterval (-5206072872 / 1000000000000) (-5206072871 / 1000000000000), orderedInterval (-45934615573 / 1000000000000) (-45934615572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (877371118869413 / 4000000000000)) (orderedInterval (11552903122 / 1000000000000) (11552903123 / 1000000000000), orderedInterval (52594326518 / 1000000000000) (52594326519 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_stateChecks3 :
    compactCertificate276.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1346112922454699 / 4000000000000)) (orderedInterval (-39924634207 / 1000000000000) (-39924634206 / 1000000000000), orderedInterval (-17196111104 / 1000000000000) (-17196111103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (777178658138771 / 4000000000000)) (orderedInterval (16952837152 / 1000000000000) (16952837153 / 1000000000000), orderedInterval (54629755969 / 1000000000000) (54629755970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1379117167049839 / 4000000000000)) (orderedInterval (-466843349 / 1000000000000) (-466843347 / 1000000000000), orderedInterval (42968571328 / 1000000000000) (42968571329 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_stateChecks4 :
    compactCertificate276.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1288550151831691 / 4000000000000)) (orderedInterval (27308492855 / 1000000000000) (27308501009 / 1000000000000), orderedInterval (-35120624077 / 1000000000000) (-35120615923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (919570189454203 / 4000000000000)) (orderedInterval (-51241520561 / 1000000000000) (-51241520559 / 1000000000000), orderedInterval (-11867973134 / 1000000000000) (-11867973131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1042694586156237 / 4000000000000)) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_stateChecks5 :
    compactCertificate276.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (869290039561853 / 4000000000000)) (orderedInterval (-52656672577 / 1000000000000) (-52656672574 / 1000000000000), orderedInterval (-12394677033 / 1000000000000) (-12394677031 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (768044112874913 / 4000000000000)) (orderedInterval (-52758378368 / 1000000000000) (-52758378367 / 1000000000000), orderedInterval (-22929550696 / 1000000000000) (-22929550695 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (222609119868387 / 800000000000)) (orderedInterval (25220594374 / 1000000000000) (25220597760 / 1000000000000), orderedInterval (-40687306798 / 1000000000000) (-40687303413 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_stateChecks6 :
    compactCertificate276.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (615748540832089 / 4000000000000)) (orderedInterval (-45394718923 / 1000000000000) (-45394718922 / 1000000000000), orderedInterval (-45403652423 / 1000000000000) (-45403652422 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (521976857291729 / 4000000000000)) (orderedInterval (-43276932122 / 1000000000000) (-43276909795 / 1000000000000), orderedInterval (54989569188 / 1000000000000) (54989591515 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (326628881130587 / 4000000000000)) (orderedInterval (60808120081 / 1000000000000) (60808120082 / 1000000000000), orderedInterval (63648188528 / 1000000000000) (63648188529 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_stateChecks7 :
    compactCertificate276.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (175662098590629 / 4000000000000)) (orderedInterval (79005497300 / 1000000000000) (79005497301 / 1000000000000), orderedInterval (89956114583 / 1000000000000) (89956114584 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (476956768818887 / 4000000000000)) (orderedInterval (43812888752 / 1000000000000) (43812888753 / 1000000000000), orderedInterval (58292420318 / 1000000000000) (58292420319 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (651243691533799 / 4000000000000)) (orderedInterval (14422209639 / 1000000000000) (14422209640 / 1000000000000), orderedInterval (60801373389 / 1000000000000) (60801373390 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_stateChecks8 :
    compactCertificate276.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (275371118869413 / 4000000000000)) (orderedInterval (47055351978 / 1000000000000) (47055351979 / 1000000000000), orderedInterval (83523419491 / 1000000000000) (83523419492 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1119368310056773 / 4000000000000)) (orderedInterval (-40773566108 / 1000000000000) (-40773566107 / 1000000000000), orderedInterval (-24674669342 / 1000000000000) (-24674669341 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (747686155041707 / 4000000000000)) (orderedInterval (-41426567453 / 1000000000000) (-41426515658 / 1000000000000), orderedInterval (41216189543 / 1000000000000) (41216241338 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_states : ∀ j,
    BesselStateValid (compactCertificate276.point j) (compactCertificate276.state j) :=
  compactCertificate276.statesValid_of_checks3 compactCertificate276_stateChecks0
    compactCertificate276_stateChecks1 compactCertificate276_stateChecks2
    compactCertificate276_stateChecks3 compactCertificate276_stateChecks4
    compactCertificate276_stateChecks5 compactCertificate276_stateChecks6
    compactCertificate276_stateChecks7 compactCertificate276_stateChecks8

theorem compactCertificate276_chunkChecks0_0 :
    compactCertificate276.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (301 / 2) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30500883754 / 1000000000000) (30500883755 / 1000000000000), orderedInterval (57342040310 / 1000000000000) (57342040311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (443430475318201 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-75276489547 / 1000000000000) (-75276489363 / 1000000000000), orderedInterval (9061481447 / 1000000000000) (9061481631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (143396304863833 / 800000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48796413322 / 1000000000000) (-48796413321 / 1000000000000), orderedInterval (-34077501969 / 1000000000000) (-34077501968 / 1000000000000)))) (orderedInterval (8524622562 / 1000000000000) (8524622576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (129391906766507 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138850702533 / 1000000000000) (138850702694 / 1000000000000), orderedInterval (-22110375813 / 1000000000000) (-22110375652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (347564862052079 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24428438873 / 1000000000000) (-24428438408 / 1000000000000), orderedInterval (82177036230 / 1000000000000) (82177036695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (943706211465843 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-46103911818 / 1000000000000) (-46103911817 / 1000000000000), orderedInterval (-23835679343 / 1000000000000) (-23835679342 / 1000000000000)))) (orderedInterval (879153896 / 1000000000000) (879153934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (695129724104459 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-59211647519 / 1000000000000) (-59211646619 / 1000000000000), orderedInterval (12711567989 / 1000000000000) (12711568889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1191116630359607 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5206072872 / 1000000000000) (-5206072871 / 1000000000000), orderedInterval (-45934615573 / 1000000000000) (-45934615572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (877371118869413 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11552903122 / 1000000000000) (11552903123 / 1000000000000), orderedInterval (52594326518 / 1000000000000) (52594326519 / 1000000000000)))) (orderedInterval (439786987 / 1000000000000) (439786996 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks0_1 :
    compactCertificate276.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1346112922454699 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39924634207 / 1000000000000) (-39924634206 / 1000000000000), orderedInterval (-17196111104 / 1000000000000) (-17196111103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (777178658138771 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16952837152 / 1000000000000) (16952837153 / 1000000000000), orderedInterval (54629755969 / 1000000000000) (54629755970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1379117167049839 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-466843349 / 1000000000000) (-466843347 / 1000000000000), orderedInterval (42968571328 / 1000000000000) (42968571329 / 1000000000000)))) (orderedInterval (8283826614 / 1000000000000) (8283826674 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1288550151831691 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27308492855 / 1000000000000) (27308501009 / 1000000000000), orderedInterval (-35120624077 / 1000000000000) (-35120615923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (919570189454203 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-51241520561 / 1000000000000) (-51241520559 / 1000000000000), orderedInterval (-11867973134 / 1000000000000) (-11867973131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000)))) (orderedInterval (-5176221229 / 1000000000000) (-5176221063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (869290039561853 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52656672577 / 1000000000000) (-52656672574 / 1000000000000), orderedInterval (-12394677033 / 1000000000000) (-12394677031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (768044112874913 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-52758378368 / 1000000000000) (-52758378367 / 1000000000000), orderedInterval (-22929550696 / 1000000000000) (-22929550695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (222609119868387 / 800000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25220594374 / 1000000000000) (25220597760 / 1000000000000), orderedInterval (-40687306798 / 1000000000000) (-40687303413 / 1000000000000)))) (orderedInterval (3056871629 / 1000000000000) (3056871731 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks0_2 :
    compactCertificate276.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (615748540832089 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45394718923 / 1000000000000) (-45394718922 / 1000000000000), orderedInterval (-45403652423 / 1000000000000) (-45403652422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (521976857291729 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43276932122 / 1000000000000) (-43276909795 / 1000000000000), orderedInterval (54989569188 / 1000000000000) (54989591515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (326628881130587 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60808120081 / 1000000000000) (60808120082 / 1000000000000), orderedInterval (63648188528 / 1000000000000) (63648188529 / 1000000000000)))) (orderedInterval (11687368462 / 1000000000000) (11687369764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (175662098590629 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79005497300 / 1000000000000) (79005497301 / 1000000000000), orderedInterval (89956114583 / 1000000000000) (89956114584 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (476956768818887 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43812888752 / 1000000000000) (43812888753 / 1000000000000), orderedInterval (58292420318 / 1000000000000) (58292420319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (651243691533799 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14422209639 / 1000000000000) (14422209640 / 1000000000000), orderedInterval (60801373389 / 1000000000000) (60801373390 / 1000000000000)))) (orderedInterval (-3558124571 / 1000000000000) (-3558124552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (275371118869413 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47055351978 / 1000000000000) (47055351979 / 1000000000000), orderedInterval (83523419491 / 1000000000000) (83523419492 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1119368310056773 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40773566108 / 1000000000000) (-40773566107 / 1000000000000), orderedInterval (-24674669342 / 1000000000000) (-24674669341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (747686155041707 / 4000000000000) 0 (IntervalRat.scale (301 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41426567453 / 1000000000000) (-41426515658 / 1000000000000), orderedInterval (41216189543 / 1000000000000) (41216241338 / 1000000000000)))) (orderedInterval (11375419069 / 1000000000000) (11375428830 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks0 :
    compactCertificate276.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate276.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate276_chunkChecks0_0
    compactCertificate276_chunkChecks0_1 compactCertificate276_chunkChecks0_2

theorem compactCertificate276_chunkChecks1_0 :
    compactCertificate276.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (301 / 2) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30500883754 / 1000000000000) (30500883755 / 1000000000000), orderedInterval (57342040310 / 1000000000000) (57342040311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (443430475318201 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-75276489547 / 1000000000000) (-75276489363 / 1000000000000), orderedInterval (9061481447 / 1000000000000) (9061481631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (143396304863833 / 800000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48796413322 / 1000000000000) (-48796413321 / 1000000000000), orderedInterval (-34077501969 / 1000000000000) (-34077501968 / 1000000000000)))) (orderedInterval (20408923097 / 1000000000000) (20408923111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (129391906766507 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138850702533 / 1000000000000) (138850702694 / 1000000000000), orderedInterval (-22110375813 / 1000000000000) (-22110375652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (347564862052079 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24428438873 / 1000000000000) (-24428438408 / 1000000000000), orderedInterval (82177036230 / 1000000000000) (82177036695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (943706211465843 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-46103911818 / 1000000000000) (-46103911817 / 1000000000000), orderedInterval (-23835679343 / 1000000000000) (-23835679342 / 1000000000000)))) (orderedInterval (4440138787 / 1000000000000) (4440138819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (695129724104459 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-59211647519 / 1000000000000) (-59211646619 / 1000000000000), orderedInterval (12711567989 / 1000000000000) (12711568889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1191116630359607 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5206072872 / 1000000000000) (-5206072871 / 1000000000000), orderedInterval (-45934615573 / 1000000000000) (-45934615572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (877371118869413 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11552903122 / 1000000000000) (11552903123 / 1000000000000), orderedInterval (52594326518 / 1000000000000) (52594326519 / 1000000000000)))) (orderedInterval (4655830837 / 1000000000000) (4655830852 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks1_1 :
    compactCertificate276.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1346112922454699 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39924634207 / 1000000000000) (-39924634206 / 1000000000000), orderedInterval (-17196111104 / 1000000000000) (-17196111103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (777178658138771 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16952837152 / 1000000000000) (16952837153 / 1000000000000), orderedInterval (54629755969 / 1000000000000) (54629755970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1379117167049839 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-466843349 / 1000000000000) (-466843347 / 1000000000000), orderedInterval (42968571328 / 1000000000000) (42968571329 / 1000000000000)))) (orderedInterval (26051156897 / 1000000000000) (26051157022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1288550151831691 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27308492855 / 1000000000000) (27308501009 / 1000000000000), orderedInterval (-35120624077 / 1000000000000) (-35120615923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (919570189454203 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-51241520561 / 1000000000000) (-51241520559 / 1000000000000), orderedInterval (-11867973134 / 1000000000000) (-11867973131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000)))) (orderedInterval (-28197330 / 1000000000000) (-28196984 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (869290039561853 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52656672577 / 1000000000000) (-52656672574 / 1000000000000), orderedInterval (-12394677033 / 1000000000000) (-12394677031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (768044112874913 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-52758378368 / 1000000000000) (-52758378367 / 1000000000000), orderedInterval (-22929550696 / 1000000000000) (-22929550695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (222609119868387 / 800000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25220594374 / 1000000000000) (25220597760 / 1000000000000), orderedInterval (-40687306798 / 1000000000000) (-40687303413 / 1000000000000)))) (orderedInterval (-458686375 / 1000000000000) (-458686193 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks1_2 :
    compactCertificate276.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (615748540832089 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45394718923 / 1000000000000) (-45394718922 / 1000000000000), orderedInterval (-45403652423 / 1000000000000) (-45403652422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (521976857291729 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43276932122 / 1000000000000) (-43276909795 / 1000000000000), orderedInterval (54989569188 / 1000000000000) (54989591515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (326628881130587 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60808120081 / 1000000000000) (60808120082 / 1000000000000), orderedInterval (63648188528 / 1000000000000) (63648188529 / 1000000000000)))) (orderedInterval (5851075585 / 1000000000000) (5851076716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (175662098590629 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79005497300 / 1000000000000) (79005497301 / 1000000000000), orderedInterval (89956114583 / 1000000000000) (89956114584 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (476956768818887 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43812888752 / 1000000000000) (43812888753 / 1000000000000), orderedInterval (58292420318 / 1000000000000) (58292420319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (651243691533799 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14422209639 / 1000000000000) (14422209640 / 1000000000000), orderedInterval (60801373389 / 1000000000000) (60801373390 / 1000000000000)))) (orderedInterval (-6573384437 / 1000000000000) (-6573384420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (275371118869413 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47055351978 / 1000000000000) (47055351979 / 1000000000000), orderedInterval (83523419491 / 1000000000000) (83523419492 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1119368310056773 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40773566108 / 1000000000000) (-40773566107 / 1000000000000), orderedInterval (-24674669342 / 1000000000000) (-24674669341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (747686155041707 / 4000000000000) 1 (IntervalRat.scale (301 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41426567453 / 1000000000000) (-41426515658 / 1000000000000), orderedInterval (41216189543 / 1000000000000) (41216241338 / 1000000000000)))) (orderedInterval (-5639667566 / 1000000000000) (-5639655436 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks1 :
    compactCertificate276.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate276.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate276_chunkChecks1_0
    compactCertificate276_chunkChecks1_1 compactCertificate276_chunkChecks1_2

theorem compactCertificate276_chunkChecks2_0 :
    compactCertificate276.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (301 / 2) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30500883754 / 1000000000000) (30500883755 / 1000000000000), orderedInterval (57342040310 / 1000000000000) (57342040311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (443430475318201 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-75276489547 / 1000000000000) (-75276489363 / 1000000000000), orderedInterval (9061481447 / 1000000000000) (9061481631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (143396304863833 / 800000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48796413322 / 1000000000000) (-48796413321 / 1000000000000), orderedInterval (-34077501969 / 1000000000000) (-34077501968 / 1000000000000)))) (orderedInterval (-7782798213 / 1000000000000) (-7782798197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (129391906766507 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138850702533 / 1000000000000) (138850702694 / 1000000000000), orderedInterval (-22110375813 / 1000000000000) (-22110375652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (347564862052079 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24428438873 / 1000000000000) (-24428438408 / 1000000000000), orderedInterval (82177036230 / 1000000000000) (82177036695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (943706211465843 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-46103911818 / 1000000000000) (-46103911817 / 1000000000000), orderedInterval (-23835679343 / 1000000000000) (-23835679342 / 1000000000000)))) (orderedInterval (-7716843711 / 1000000000000) (-7716843675 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (695129724104459 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-59211647519 / 1000000000000) (-59211646619 / 1000000000000), orderedInterval (12711567989 / 1000000000000) (12711568889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1191116630359607 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5206072872 / 1000000000000) (-5206072871 / 1000000000000), orderedInterval (-45934615573 / 1000000000000) (-45934615572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (877371118869413 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11552903122 / 1000000000000) (11552903123 / 1000000000000), orderedInterval (52594326518 / 1000000000000) (52594326519 / 1000000000000)))) (orderedInterval (-1252637935 / 1000000000000) (-1252637908 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks2_1 :
    compactCertificate276.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1346112922454699 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39924634207 / 1000000000000) (-39924634206 / 1000000000000), orderedInterval (-17196111104 / 1000000000000) (-17196111103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (777178658138771 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16952837152 / 1000000000000) (16952837153 / 1000000000000), orderedInterval (54629755969 / 1000000000000) (54629755970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1379117167049839 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-466843349 / 1000000000000) (-466843347 / 1000000000000), orderedInterval (42968571328 / 1000000000000) (42968571329 / 1000000000000)))) (orderedInterval (-37388874132 / 1000000000000) (-37388873863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1288550151831691 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27308492855 / 1000000000000) (27308501009 / 1000000000000), orderedInterval (-35120624077 / 1000000000000) (-35120615923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (919570189454203 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-51241520561 / 1000000000000) (-51241520559 / 1000000000000), orderedInterval (-11867973134 / 1000000000000) (-11867973131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000)))) (orderedInterval (13078181046 / 1000000000000) (13078181772 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (869290039561853 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52656672577 / 1000000000000) (-52656672574 / 1000000000000), orderedInterval (-12394677033 / 1000000000000) (-12394677031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (768044112874913 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-52758378368 / 1000000000000) (-52758378367 / 1000000000000), orderedInterval (-22929550696 / 1000000000000) (-22929550695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (222609119868387 / 800000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25220594374 / 1000000000000) (25220597760 / 1000000000000), orderedInterval (-40687306798 / 1000000000000) (-40687303413 / 1000000000000)))) (orderedInterval (-5850913524 / 1000000000000) (-5850913195 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks2_2 :
    compactCertificate276.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (615748540832089 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45394718923 / 1000000000000) (-45394718922 / 1000000000000), orderedInterval (-45403652423 / 1000000000000) (-45403652422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (521976857291729 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43276932122 / 1000000000000) (-43276909795 / 1000000000000), orderedInterval (54989569188 / 1000000000000) (54989591515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (326628881130587 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60808120081 / 1000000000000) (60808120082 / 1000000000000), orderedInterval (63648188528 / 1000000000000) (63648188529 / 1000000000000)))) (orderedInterval (-10056782670 / 1000000000000) (-10056781678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (175662098590629 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79005497300 / 1000000000000) (79005497301 / 1000000000000), orderedInterval (89956114583 / 1000000000000) (89956114584 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (476956768818887 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43812888752 / 1000000000000) (43812888753 / 1000000000000), orderedInterval (58292420318 / 1000000000000) (58292420319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (651243691533799 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14422209639 / 1000000000000) (14422209640 / 1000000000000), orderedInterval (60801373389 / 1000000000000) (60801373390 / 1000000000000)))) (orderedInterval (2085354869 / 1000000000000) (2085354886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (275371118869413 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47055351978 / 1000000000000) (47055351979 / 1000000000000), orderedInterval (83523419491 / 1000000000000) (83523419492 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1119368310056773 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40773566108 / 1000000000000) (-40773566107 / 1000000000000), orderedInterval (-24674669342 / 1000000000000) (-24674669341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (747686155041707 / 4000000000000) 2 (IntervalRat.scale (301 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41426567453 / 1000000000000) (-41426515658 / 1000000000000), orderedInterval (41216189543 / 1000000000000) (41216241338 / 1000000000000)))) (orderedInterval (-23487214384 / 1000000000000) (-23487199225 / 1000000000000))) = true
  rfl'

theorem compactCertificate276_chunkChecks2 :
    compactCertificate276.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate276.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate276_chunkChecks2_0
    compactCertificate276_chunkChecks2_1 compactCertificate276_chunkChecks2_2

theorem compactCertificate276_chunkChecks3_0 :
    compactCertificate276.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (301 / 2) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30500883754 / 1000000000000) (30500883755 / 1000000000000), orderedInterval (57342040310 / 1000000000000) (57342040311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (443430475318201 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-75276489547 / 1000000000000) (-75276489363 / 1000000000000), orderedInterval (9061481447 / 1000000000000) (9061481631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (143396304863833 / 800000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48796413322 / 1000000000000) (-48796413321 / 1000000000000), orderedInterval (-34077501969 / 1000000000000) (-34077501968 / 1000000000000)))) (orderedInterval (-19331189159 / 1000000000000) (-19331189141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (129391906766507 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138850702533 / 1000000000000) (138850702694 / 1000000000000), orderedInterval (-22110375813 / 1000000000000) (-22110375652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (347564862052079 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24428438873 / 1000000000000) (-24428438408 / 1000000000000), orderedInterval (82177036230 / 1000000000000) (82177036695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (943706211465843 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-46103911818 / 1000000000000) (-46103911817 / 1000000000000), orderedInterval (-23835679343 / 1000000000000) (-23835679342 / 1000000000000)))) (orderedInterval (-7055963045 / 1000000000000) (-7055962998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (695129724104459 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-59211647519 / 1000000000000) (-59211646619 / 1000000000000), orderedInterval (12711567989 / 1000000000000) (12711568889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1191116630359607 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5206072872 / 1000000000000) (-5206072871 / 1000000000000), orderedInterval (-45934615573 / 1000000000000) (-45934615572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (877371118869413 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11552903122 / 1000000000000) (11552903123 / 1000000000000), orderedInterval (52594326518 / 1000000000000) (52594326519 / 1000000000000)))) (orderedInterval (-14900919962 / 1000000000000) (-14900919914 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate276_chunkChecks3_1 :
    compactCertificate276.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1346112922454699 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39924634207 / 1000000000000) (-39924634206 / 1000000000000), orderedInterval (-17196111104 / 1000000000000) (-17196111103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (777178658138771 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16952837152 / 1000000000000) (16952837153 / 1000000000000), orderedInterval (54629755969 / 1000000000000) (54629755970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1379117167049839 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-466843349 / 1000000000000) (-466843347 / 1000000000000), orderedInterval (42968571328 / 1000000000000) (42968571329 / 1000000000000)))) (orderedInterval (-116061005925 / 1000000000000) (-116061005340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1288550151831691 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27308492855 / 1000000000000) (27308501009 / 1000000000000), orderedInterval (-35120624077 / 1000000000000) (-35120615923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (919570189454203 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-51241520561 / 1000000000000) (-51241520559 / 1000000000000), orderedInterval (-11867973134 / 1000000000000) (-11867973131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000)))) (orderedInterval (-3291486783 / 1000000000000) (-3291485251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (869290039561853 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52656672577 / 1000000000000) (-52656672574 / 1000000000000), orderedInterval (-12394677033 / 1000000000000) (-12394677031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (768044112874913 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-52758378368 / 1000000000000) (-52758378367 / 1000000000000), orderedInterval (-22929550696 / 1000000000000) (-22929550695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (222609119868387 / 800000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25220594374 / 1000000000000) (25220597760 / 1000000000000), orderedInterval (-40687306798 / 1000000000000) (-40687303413 / 1000000000000)))) (orderedInterval (4329220797 / 1000000000000) (4329221396 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate276_chunkChecks3_2 :
    compactCertificate276.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (615748540832089 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45394718923 / 1000000000000) (-45394718922 / 1000000000000), orderedInterval (-45403652423 / 1000000000000) (-45403652422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (521976857291729 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43276932122 / 1000000000000) (-43276909795 / 1000000000000), orderedInterval (54989569188 / 1000000000000) (54989591515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (326628881130587 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60808120081 / 1000000000000) (60808120082 / 1000000000000), orderedInterval (63648188528 / 1000000000000) (63648188529 / 1000000000000)))) (orderedInterval (-6003524065 / 1000000000000) (-6003523202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (175662098590629 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79005497300 / 1000000000000) (79005497301 / 1000000000000), orderedInterval (89956114583 / 1000000000000) (89956114584 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (476956768818887 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43812888752 / 1000000000000) (43812888753 / 1000000000000), orderedInterval (58292420318 / 1000000000000) (58292420319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (651243691533799 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14422209639 / 1000000000000) (14422209640 / 1000000000000), orderedInterval (60801373389 / 1000000000000) (60801373390 / 1000000000000)))) (orderedInterval (6584174706 / 1000000000000) (6584174724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (275371118869413 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47055351978 / 1000000000000) (47055351979 / 1000000000000), orderedInterval (83523419491 / 1000000000000) (83523419492 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1119368310056773 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40773566108 / 1000000000000) (-40773566107 / 1000000000000), orderedInterval (-24674669342 / 1000000000000) (-24674669341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (747686155041707 / 4000000000000) 3 (IntervalRat.scale (301 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41426567453 / 1000000000000) (-41426515658 / 1000000000000), orderedInterval (41216189543 / 1000000000000) (41216241338 / 1000000000000)))) (orderedInterval (2010976584 / 1000000000000) (2010995436 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate276_chunkChecks3 :
    compactCertificate276.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate276.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate276_chunkChecks3_0
    compactCertificate276_chunkChecks3_1 compactCertificate276_chunkChecks3_2

theorem compactCertificate276_chunkChecks4_0 :
    compactCertificate276.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (301 / 2) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30500883754 / 1000000000000) (30500883755 / 1000000000000), orderedInterval (57342040310 / 1000000000000) (57342040311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (443430475318201 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-75276489547 / 1000000000000) (-75276489363 / 1000000000000), orderedInterval (9061481447 / 1000000000000) (9061481631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (143396304863833 / 800000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48796413322 / 1000000000000) (-48796413321 / 1000000000000), orderedInterval (-34077501969 / 1000000000000) (-34077501968 / 1000000000000)))) (orderedInterval (6378077730 / 1000000000000) (6378077750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (129391906766507 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (138850702533 / 1000000000000) (138850702694 / 1000000000000), orderedInterval (-22110375813 / 1000000000000) (-22110375652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (347564862052079 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24428438873 / 1000000000000) (-24428438408 / 1000000000000), orderedInterval (82177036230 / 1000000000000) (82177036695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (943706211465843 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-46103911818 / 1000000000000) (-46103911817 / 1000000000000), orderedInterval (-23835679343 / 1000000000000) (-23835679342 / 1000000000000)))) (orderedInterval (19783822751 / 1000000000000) (19783822820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (695129724104459 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-59211647519 / 1000000000000) (-59211646619 / 1000000000000), orderedInterval (12711567989 / 1000000000000) (12711568889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1191116630359607 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5206072872 / 1000000000000) (-5206072871 / 1000000000000), orderedInterval (-45934615573 / 1000000000000) (-45934615572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (877371118869413 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11552903122 / 1000000000000) (11552903123 / 1000000000000), orderedInterval (52594326518 / 1000000000000) (52594326519 / 1000000000000)))) (orderedInterval (3918701601 / 1000000000000) (3918701690 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate276_chunkChecks4_1 :
    compactCertificate276.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1346112922454699 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-39924634207 / 1000000000000) (-39924634206 / 1000000000000), orderedInterval (-17196111104 / 1000000000000) (-17196111103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (777178658138771 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16952837152 / 1000000000000) (16952837153 / 1000000000000), orderedInterval (54629755969 / 1000000000000) (54629755970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1379117167049839 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-466843349 / 1000000000000) (-466843347 / 1000000000000), orderedInterval (42968571328 / 1000000000000) (42968571329 / 1000000000000)))) (orderedInterval (180554977945 / 1000000000000) (180554979247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1288550151831691 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27308492855 / 1000000000000) (27308501009 / 1000000000000), orderedInterval (-35120624077 / 1000000000000) (-35120615923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (919570189454203 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-51241520561 / 1000000000000) (-51241520559 / 1000000000000), orderedInterval (-11867973134 / 1000000000000) (-11867973131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1042694586156237 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32076692463 / 1000000000000) (-32076692462 / 1000000000000), orderedInterval (-37532309014 / 1000000000000) (-37532309013 / 1000000000000)))) (orderedInterval (-35224335422 / 1000000000000) (-35224332169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (869290039561853 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52656672577 / 1000000000000) (-52656672574 / 1000000000000), orderedInterval (-12394677033 / 1000000000000) (-12394677031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (768044112874913 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-52758378368 / 1000000000000) (-52758378367 / 1000000000000), orderedInterval (-22929550696 / 1000000000000) (-22929550695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (222609119868387 / 800000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25220594374 / 1000000000000) (25220597760 / 1000000000000), orderedInterval (-40687306798 / 1000000000000) (-40687303413 / 1000000000000)))) (orderedInterval (12843895101 / 1000000000000) (12843896199 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate276_chunkChecks4_2 :
    compactCertificate276.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (615748540832089 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45394718923 / 1000000000000) (-45394718922 / 1000000000000), orderedInterval (-45403652423 / 1000000000000) (-45403652422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (521976857291729 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43276932122 / 1000000000000) (-43276909795 / 1000000000000), orderedInterval (54989569188 / 1000000000000) (54989591515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (326628881130587 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60808120081 / 1000000000000) (60808120082 / 1000000000000), orderedInterval (63648188528 / 1000000000000) (63648188529 / 1000000000000)))) (orderedInterval (9579785598 / 1000000000000) (9579786356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (175662098590629 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79005497300 / 1000000000000) (79005497301 / 1000000000000), orderedInterval (89956114583 / 1000000000000) (89956114584 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (476956768818887 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43812888752 / 1000000000000) (43812888753 / 1000000000000), orderedInterval (58292420318 / 1000000000000) (58292420319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (651243691533799 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14422209639 / 1000000000000) (14422209640 / 1000000000000), orderedInterval (60801373389 / 1000000000000) (60801373390 / 1000000000000)))) (orderedInterval (-2003439085 / 1000000000000) (-2003439066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (275371118869413 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47055351978 / 1000000000000) (47055351979 / 1000000000000), orderedInterval (83523419491 / 1000000000000) (83523419492 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1119368310056773 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-40773566108 / 1000000000000) (-40773566107 / 1000000000000), orderedInterval (-24674669342 / 1000000000000) (-24674669341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (747686155041707 / 4000000000000) 4 (IntervalRat.scale (301 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41426567453 / 1000000000000) (-41426515658 / 1000000000000), orderedInterval (41216189543 / 1000000000000) (41216241338 / 1000000000000)))) (orderedInterval (58155229217 / 1000000000000) (58155252802 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate276_chunkChecks4 :
    compactCertificate276.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate276.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate276_chunkChecks4_0
    compactCertificate276_chunkChecks4_1 compactCertificate276_chunkChecks4_2

theorem compactCertificate276_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate276.chunkCheck r b = true :=
  compactCertificate276.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate276_chunkChecks0
    · exact compactCertificate276_chunkChecks1
    · exact compactCertificate276_chunkChecks2
    · exact compactCertificate276_chunkChecks3
    · exact compactCertificate276_chunkChecks4)

theorem compactCertificate276_coefficient0 :
    compactCertificate276.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate276_coefficient1 :
    compactCertificate276.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate276_coefficient2 :
    compactCertificate276.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate276_coefficient3 :
    compactCertificate276.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate276_coefficient4 :
    compactCertificate276.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate276_coefficients : ∀ r : Fin 5,
    compactCertificate276.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate276_coefficient0
  · exact compactCertificate276_coefficient1
  · exact compactCertificate276_coefficient2
  · exact compactCertificate276_coefficient3
  · exact compactCertificate276_coefficient4

theorem compactCertificate276_lower : (1 : ℚ) ≤ compactCertificate276.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate276, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate276_proves {t : ℝ} (ht : t ∈ compactCertificate276.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate276.proves compactCertificate276_states compactCertificate276_chunks
    compactCertificate276_coefficients compactCertificate276_lower ht

end Erdos232
