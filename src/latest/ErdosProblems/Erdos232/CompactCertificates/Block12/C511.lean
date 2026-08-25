/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate511 : CompactCertificate where
  left := 382
  right := 383
  center := 765 / 2
  grid := fun i =>
    match i.val with
    | 0 => 122
    | 1 => 90
    | 2 => 145
    | 3 => 26
    | 4 => 70
    | 5 => 191
    | 6 => 141
    | 7 => 241
    | 8 => 178
    | 9 => 272
    | 10 => 157
    | 11 => 279
    | 12 => 261
    | 13 => 186
    | 14 => 211
    | 15 => 176
    | 16 => 155
    | 17 => 225
    | 18 => 125
    | 19 => 106
    | 20 => 66
    | 21 => 36
    | 22 => 97
    | 23 => 132
    | 24 => 56
    | 25 => 227
    | _ => 151
  point := fun i =>
    match i.val with
    | 0 => 765 / 2
    | 1 => 225398215028853 / 800000000000
    | 2 => 72889151641749 / 160000000000
    | 3 => 65770636994271 / 800000000000
    | 4 => 176669182371987 / 800000000000
    | 5 => 479691197190279 / 800000000000
    | 6 => 353338364744127 / 800000000000
    | 7 => 605451310448571 / 800000000000
    | 8 => 445972694973489 / 800000000000
    | 9 => 684236801114847 / 800000000000
    | 10 => 395044301313063 / 800000000000
    | 11 => 701013045045267 / 800000000000
    | 12 => 654977319701823 / 800000000000
    | 13 => 467422720885359 / 800000000000
    | 14 => 530007547115961 / 800000000000
    | 15 => 441865036720809 / 800000000000
    | 16 => 390401160364989 / 800000000000
    | 17 => 113153472889911 / 160000000000
    | 18 => 312988460954517 / 800000000000
    | 19 => 265323784603437 / 800000000000
    | 20 => 166027305026511 / 800000000000
    | 21 => 89290036825137 / 800000000000
    | 22 => 242439819366411 / 800000000000
    | 23 => 331030846527147 / 800000000000
    | 24 => 139972694973489 / 800000000000
    | 25 => 568981234015569 / 800000000000
    | _ => 380053095419871 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (439274361 / 1000000000000) (439274362 / 1000000000000), orderedInterval (40793713102 / 1000000000000) (40793713103 / 1000000000000))
    | 1 => (orderedInterval (-9937663878 / 1000000000000) (-9937663837 / 1000000000000), orderedInterval (46501869786 / 1000000000000) (46501869827 / 1000000000000))
    | 2 => (orderedInterval (-27111391626 / 1000000000000) (-27111391625 / 1000000000000), orderedInterval (-25707869886 / 1000000000000) (-25707869885 / 1000000000000))
    | 3 => (orderedInterval (85150214874 / 1000000000000) (85150214875 / 1000000000000), orderedInterval (21681920994 / 1000000000000) (21681920996 / 1000000000000))
    | 4 => (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))
    | 5 => (orderedInterval (-11325551417 / 1000000000000) (-11325551416 / 1000000000000), orderedInterval (-30542939880 / 1000000000000) (-30542939879 / 1000000000000))
    | 6 => (orderedInterval (18417596849 / 1000000000000) (18417597597 / 1000000000000), orderedInterval (-33219876255 / 1000000000000) (-33219875507 / 1000000000000))
    | 7 => (orderedInterval (-13278228219 / 1000000000000) (-13278228218 / 1000000000000), orderedInterval (-25776349918 / 1000000000000) (-25776349917 / 1000000000000))
    | 8 => (orderedInterval (-27536099890 / 1000000000000) (-27536058145 / 1000000000000), orderedInterval (19614289832 / 1000000000000) (19614331577 / 1000000000000))
    | 9 => (orderedInterval (27282246869 / 1000000000000) (27282250952 / 1000000000000), orderedInterval (58930614 / 1000000000000) (58934698 / 1000000000000))
    | 10 => (orderedInterval (-35114368582 / 1000000000000) (-35114368555 / 1000000000000), orderedInterval (-7460605926 / 1000000000000) (-7460605899 / 1000000000000))
    | 11 => (orderedInterval (-14024338843 / 1000000000000) (-14024338842 / 1000000000000), orderedInterval (-23010077788 / 1000000000000) (-23010077787 / 1000000000000))
    | 12 => (orderedInterval (12098594101 / 1000000000000) (12098594125 / 1000000000000), orderedInterval (-25131120581 / 1000000000000) (-25131120556 / 1000000000000))
    | 13 => (orderedInterval (21947366453 / 1000000000000) (21947366454 / 1000000000000), orderedInterval (24636767124 / 1000000000000) (24636767125 / 1000000000000))
    | 14 => (orderedInterval (-12600234444 / 1000000000000) (-12600234443 / 1000000000000), orderedInterval (-28312850907 / 1000000000000) (-28312850906 / 1000000000000))
    | 15 => (orderedInterval (6617034614 / 1000000000000) (6617034615 / 1000000000000), orderedInterval (33292962072 / 1000000000000) (33292962073 / 1000000000000))
    | 16 => (orderedInterval (-34820180619 / 1000000000000) (-34820170748 / 1000000000000), orderedInterval (9632525076 / 1000000000000) (9632534947 / 1000000000000))
    | 17 => (orderedInterval (-27212492387 / 1000000000000) (-27212492382 / 1000000000000), orderedInterval (-12616663372 / 1000000000000) (-12616663368 / 1000000000000))
    | 18 => (orderedInterval (25315245172 / 1000000000000) (25315251955 / 1000000000000), orderedInterval (-31438432748 / 1000000000000) (-31438425965 / 1000000000000))
    | 19 => (orderedInterval (-23608217504 / 1000000000000) (-23608214576 / 1000000000000), orderedInterval (36943295499 / 1000000000000) (36943298427 / 1000000000000))
    | 20 => (orderedInterval (45805577804 / 1000000000000) (45805577805 / 1000000000000), orderedInterval (31024644912 / 1000000000000) (31024644913 / 1000000000000))
    | 21 => (orderedInterval (-48683032091 / 1000000000000) (-48682999276 / 1000000000000), orderedInterval (57957227685 / 1000000000000) (57957260500 / 1000000000000))
    | 22 => (orderedInterval (35894786992 / 1000000000000) (35894868009 / 1000000000000), orderedInterval (-28559628111 / 1000000000000) (-28559547094 / 1000000000000))
    | 23 => (orderedInterval (-4562215878 / 1000000000000) (-4562215874 / 1000000000000), orderedInterval (38963207245 / 1000000000000) (38963207248 / 1000000000000))
    | 24 => (orderedInterval (-10718143571 / 1000000000000) (-10718143514 / 1000000000000), orderedInterval (59391156529 / 1000000000000) (59391156586 / 1000000000000))
    | 25 => (orderedInterval (27055400133 / 1000000000000) (27055498681 / 1000000000000), orderedInterval (-12790274925 / 1000000000000) (-12790176377 / 1000000000000))
    | _ => (orderedInterval (-36424798298 / 1000000000000) (-36424798178 / 1000000000000), orderedInterval (-3608341200 / 1000000000000) (-3608341080 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1509414150 / 1000000000000) (-1509414123 / 1000000000000)
      | 1 => orderedInterval (1822758573 / 1000000000000) (1822758638 / 1000000000000)
      | 2 => orderedInterval (-255939532 / 1000000000000) (-255938501 / 1000000000000)
      | 3 => orderedInterval (-9443054818 / 1000000000000) (-9443053939 / 1000000000000)
      | 4 => orderedInterval (1920753334 / 1000000000000) (1920753380 / 1000000000000)
      | 5 => orderedInterval (1372306684 / 1000000000000) (1372307286 / 1000000000000)
      | 6 => orderedInterval (-1220280598 / 1000000000000) (-1220279252 / 1000000000000)
      | 7 => orderedInterval (434238407 / 1000000000000) (434240897 / 1000000000000)
      | _ => orderedInterval (4567280170 / 1000000000000) (4567288322 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14691669686 / 1000000000000) (14691669718 / 1000000000000)
      | 1 => orderedInterval (3193802254 / 1000000000000) (3193802318 / 1000000000000)
      | 2 => orderedInterval (2263953606 / 1000000000000) (2263955114 / 1000000000000)
      | 3 => orderedInterval (-8230588856 / 1000000000000) (-8230586917 / 1000000000000)
      | 4 => orderedInterval (4777987544 / 1000000000000) (4777987619 / 1000000000000)
      | 5 => orderedInterval (-745391133 / 1000000000000) (-745390358 / 1000000000000)
      | 6 => orderedInterval (3876539266 / 1000000000000) (3876540609 / 1000000000000)
      | 7 => orderedInterval (-3029293648 / 1000000000000) (-3029291973 / 1000000000000)
      | _ => orderedInterval (2940552056 / 1000000000000) (2940567150 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (2094416771 / 1000000000000) (2094416807 / 1000000000000)
      | 1 => orderedInterval (-2591367762 / 1000000000000) (-2591367683 / 1000000000000)
      | 2 => orderedInterval (-195694006 / 1000000000000) (-195691793 / 1000000000000)
      | 3 => orderedInterval (39059298984 / 1000000000000) (39059303293 / 1000000000000)
      | 4 => orderedInterval (-4045716706 / 1000000000000) (-4045716581 / 1000000000000)
      | 5 => orderedInterval (-1019026598 / 1000000000000) (-1019025597 / 1000000000000)
      | 6 => orderedInterval (2780996005 / 1000000000000) (2780997353 / 1000000000000)
      | 7 => orderedInterval (33371066 / 1000000000000) (33372317 / 1000000000000)
      | _ => orderedInterval (-2922019094 / 1000000000000) (-2921991064 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13799164552 / 1000000000000) (-13799164511 / 1000000000000)
      | 1 => orderedInterval (-8302203127 / 1000000000000) (-8302203014 / 1000000000000)
      | 2 => orderedInterval (-7625329591 / 1000000000000) (-7625326341 / 1000000000000)
      | 3 => orderedInterval (40531827220 / 1000000000000) (40531836825 / 1000000000000)
      | 4 => orderedInterval (-13486708797 / 1000000000000) (-13486708585 / 1000000000000)
      | 5 => orderedInterval (2031562143 / 1000000000000) (2031563441 / 1000000000000)
      | 6 => orderedInterval (-4184605010 / 1000000000000) (-4184603655 / 1000000000000)
      | 7 => orderedInterval (3484707053 / 1000000000000) (3484708029 / 1000000000000)
      | _ => orderedInterval (-8017045930 / 1000000000000) (-8016993904 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2982058429 / 1000000000000) (-2982058381 / 1000000000000)
      | 1 => orderedInterval (5119271707 / 1000000000000) (5119271876 / 1000000000000)
      | 2 => orderedInterval (3314168292 / 1000000000000) (3314173084 / 1000000000000)
      | 3 => orderedInterval (-183543569933 / 1000000000000) (-183543548466 / 1000000000000)
      | 4 => orderedInterval (7359157934 / 1000000000000) (7359158304 / 1000000000000)
      | 5 => orderedInterval (-2541151259 / 1000000000000) (-2541149562 / 1000000000000)
      | 6 => orderedInterval (-3523952612 / 1000000000000) (-3523951244 / 1000000000000)
      | 7 => orderedInterval (146285917 / 1000000000000) (146286695 / 1000000000000)
      | _ => orderedInterval (-10025243242 / 1000000000000) (-10025146482 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2311351930 / 1000000000000) (-2311337292 / 1000000000000)
    | 1 => orderedInterval (19739230775 / 1000000000000) (19739253280 / 1000000000000)
    | 2 => orderedInterval (33194258660 / 1000000000000) (33194297052 / 1000000000000)
    | 3 => orderedInterval (-9366960591 / 1000000000000) (-9366891715 / 1000000000000)
    | _ => orderedInterval (-186677091625 / 1000000000000) (-186676964176 / 1000000000000)

theorem compactCertificate511_stateChecks0 :
    compactCertificate511.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (765 / 2)) (orderedInterval (439274361 / 1000000000000) (439274362 / 1000000000000), orderedInterval (40793713102 / 1000000000000) (40793713103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (225398215028853 / 800000000000)) (orderedInterval (-9937663878 / 1000000000000) (-9937663837 / 1000000000000), orderedInterval (46501869786 / 1000000000000) (46501869827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (72889151641749 / 160000000000)) (orderedInterval (-27111391626 / 1000000000000) (-27111391625 / 1000000000000), orderedInterval (-25707869886 / 1000000000000) (-25707869885 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_stateChecks1 :
    compactCertificate511.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (65770636994271 / 800000000000)) (orderedInterval (85150214874 / 1000000000000) (85150214875 / 1000000000000), orderedInterval (21681920994 / 1000000000000) (21681920996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176669182371987 / 800000000000)) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (479691197190279 / 800000000000)) (orderedInterval (-11325551417 / 1000000000000) (-11325551416 / 1000000000000), orderedInterval (-30542939880 / 1000000000000) (-30542939879 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_stateChecks2 :
    compactCertificate511.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (353338364744127 / 800000000000)) (orderedInterval (18417596849 / 1000000000000) (18417597597 / 1000000000000), orderedInterval (-33219876255 / 1000000000000) (-33219875507 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (605451310448571 / 800000000000)) (orderedInterval (-13278228219 / 1000000000000) (-13278228218 / 1000000000000), orderedInterval (-25776349918 / 1000000000000) (-25776349917 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (445972694973489 / 800000000000)) (orderedInterval (-27536099890 / 1000000000000) (-27536058145 / 1000000000000), orderedInterval (19614289832 / 1000000000000) (19614331577 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_stateChecks3 :
    compactCertificate511.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (684236801114847 / 800000000000)) (orderedInterval (27282246869 / 1000000000000) (27282250952 / 1000000000000), orderedInterval (58930614 / 1000000000000) (58934698 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (395044301313063 / 800000000000)) (orderedInterval (-35114368582 / 1000000000000) (-35114368555 / 1000000000000), orderedInterval (-7460605926 / 1000000000000) (-7460605899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (701013045045267 / 800000000000)) (orderedInterval (-14024338843 / 1000000000000) (-14024338842 / 1000000000000), orderedInterval (-23010077788 / 1000000000000) (-23010077787 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_stateChecks4 :
    compactCertificate511.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (654977319701823 / 800000000000)) (orderedInterval (12098594101 / 1000000000000) (12098594125 / 1000000000000), orderedInterval (-25131120581 / 1000000000000) (-25131120556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (467422720885359 / 800000000000)) (orderedInterval (21947366453 / 1000000000000) (21947366454 / 1000000000000), orderedInterval (24636767124 / 1000000000000) (24636767125 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (530007547115961 / 800000000000)) (orderedInterval (-12600234444 / 1000000000000) (-12600234443 / 1000000000000), orderedInterval (-28312850907 / 1000000000000) (-28312850906 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_stateChecks5 :
    compactCertificate511.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (441865036720809 / 800000000000)) (orderedInterval (6617034614 / 1000000000000) (6617034615 / 1000000000000), orderedInterval (33292962072 / 1000000000000) (33292962073 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (390401160364989 / 800000000000)) (orderedInterval (-34820180619 / 1000000000000) (-34820170748 / 1000000000000), orderedInterval (9632525076 / 1000000000000) (9632534947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (113153472889911 / 160000000000)) (orderedInterval (-27212492387 / 1000000000000) (-27212492382 / 1000000000000), orderedInterval (-12616663372 / 1000000000000) (-12616663368 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_stateChecks6 :
    compactCertificate511.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (312988460954517 / 800000000000)) (orderedInterval (25315245172 / 1000000000000) (25315251955 / 1000000000000), orderedInterval (-31438432748 / 1000000000000) (-31438425965 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (265323784603437 / 800000000000)) (orderedInterval (-23608217504 / 1000000000000) (-23608214576 / 1000000000000), orderedInterval (36943295499 / 1000000000000) (36943298427 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (166027305026511 / 800000000000)) (orderedInterval (45805577804 / 1000000000000) (45805577805 / 1000000000000), orderedInterval (31024644912 / 1000000000000) (31024644913 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_stateChecks7 :
    compactCertificate511.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (89290036825137 / 800000000000)) (orderedInterval (-48683032091 / 1000000000000) (-48682999276 / 1000000000000), orderedInterval (57957227685 / 1000000000000) (57957260500 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (242439819366411 / 800000000000)) (orderedInterval (35894786992 / 1000000000000) (35894868009 / 1000000000000), orderedInterval (-28559628111 / 1000000000000) (-28559547094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (331030846527147 / 800000000000)) (orderedInterval (-4562215878 / 1000000000000) (-4562215874 / 1000000000000), orderedInterval (38963207245 / 1000000000000) (38963207248 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_stateChecks8 :
    compactCertificate511.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (139972694973489 / 800000000000)) (orderedInterval (-10718143571 / 1000000000000) (-10718143514 / 1000000000000), orderedInterval (59391156529 / 1000000000000) (59391156586 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (568981234015569 / 800000000000)) (orderedInterval (27055400133 / 1000000000000) (27055498681 / 1000000000000), orderedInterval (-12790274925 / 1000000000000) (-12790176377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (380053095419871 / 800000000000)) (orderedInterval (-36424798298 / 1000000000000) (-36424798178 / 1000000000000), orderedInterval (-3608341200 / 1000000000000) (-3608341080 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_states : ∀ j,
    BesselStateValid (compactCertificate511.point j) (compactCertificate511.state j) :=
  compactCertificate511.statesValid_of_checks3 compactCertificate511_stateChecks0
    compactCertificate511_stateChecks1 compactCertificate511_stateChecks2
    compactCertificate511_stateChecks3 compactCertificate511_stateChecks4
    compactCertificate511_stateChecks5 compactCertificate511_stateChecks6
    compactCertificate511_stateChecks7 compactCertificate511_stateChecks8

theorem compactCertificate511_chunkChecks0_0 :
    compactCertificate511.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (765 / 2) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (439274361 / 1000000000000) (439274362 / 1000000000000), orderedInterval (40793713102 / 1000000000000) (40793713103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (225398215028853 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9937663878 / 1000000000000) (-9937663837 / 1000000000000), orderedInterval (46501869786 / 1000000000000) (46501869827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (72889151641749 / 160000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27111391626 / 1000000000000) (-27111391625 / 1000000000000), orderedInterval (-25707869886 / 1000000000000) (-25707869885 / 1000000000000)))) (orderedInterval (-1509414150 / 1000000000000) (-1509414123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (65770636994271 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85150214874 / 1000000000000) (85150214875 / 1000000000000), orderedInterval (21681920994 / 1000000000000) (21681920996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (479691197190279 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11325551417 / 1000000000000) (-11325551416 / 1000000000000), orderedInterval (-30542939880 / 1000000000000) (-30542939879 / 1000000000000)))) (orderedInterval (1822758573 / 1000000000000) (1822758638 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (353338364744127 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18417596849 / 1000000000000) (18417597597 / 1000000000000), orderedInterval (-33219876255 / 1000000000000) (-33219875507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (605451310448571 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13278228219 / 1000000000000) (-13278228218 / 1000000000000), orderedInterval (-25776349918 / 1000000000000) (-25776349917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (445972694973489 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27536099890 / 1000000000000) (-27536058145 / 1000000000000), orderedInterval (19614289832 / 1000000000000) (19614331577 / 1000000000000)))) (orderedInterval (-255939532 / 1000000000000) (-255938501 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks0_1 :
    compactCertificate511.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (684236801114847 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27282246869 / 1000000000000) (27282250952 / 1000000000000), orderedInterval (58930614 / 1000000000000) (58934698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (395044301313063 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35114368582 / 1000000000000) (-35114368555 / 1000000000000), orderedInterval (-7460605926 / 1000000000000) (-7460605899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (701013045045267 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14024338843 / 1000000000000) (-14024338842 / 1000000000000), orderedInterval (-23010077788 / 1000000000000) (-23010077787 / 1000000000000)))) (orderedInterval (-9443054818 / 1000000000000) (-9443053939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (654977319701823 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12098594101 / 1000000000000) (12098594125 / 1000000000000), orderedInterval (-25131120581 / 1000000000000) (-25131120556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (467422720885359 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21947366453 / 1000000000000) (21947366454 / 1000000000000), orderedInterval (24636767124 / 1000000000000) (24636767125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (530007547115961 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12600234444 / 1000000000000) (-12600234443 / 1000000000000), orderedInterval (-28312850907 / 1000000000000) (-28312850906 / 1000000000000)))) (orderedInterval (1920753334 / 1000000000000) (1920753380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (441865036720809 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6617034614 / 1000000000000) (6617034615 / 1000000000000), orderedInterval (33292962072 / 1000000000000) (33292962073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (390401160364989 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34820180619 / 1000000000000) (-34820170748 / 1000000000000), orderedInterval (9632525076 / 1000000000000) (9632534947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (113153472889911 / 160000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27212492387 / 1000000000000) (-27212492382 / 1000000000000), orderedInterval (-12616663372 / 1000000000000) (-12616663368 / 1000000000000)))) (orderedInterval (1372306684 / 1000000000000) (1372307286 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks0_2 :
    compactCertificate511.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (312988460954517 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25315245172 / 1000000000000) (25315251955 / 1000000000000), orderedInterval (-31438432748 / 1000000000000) (-31438425965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (265323784603437 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-23608217504 / 1000000000000) (-23608214576 / 1000000000000), orderedInterval (36943295499 / 1000000000000) (36943298427 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (166027305026511 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45805577804 / 1000000000000) (45805577805 / 1000000000000), orderedInterval (31024644912 / 1000000000000) (31024644913 / 1000000000000)))) (orderedInterval (-1220280598 / 1000000000000) (-1220279252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (89290036825137 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48683032091 / 1000000000000) (-48682999276 / 1000000000000), orderedInterval (57957227685 / 1000000000000) (57957260500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (242439819366411 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35894786992 / 1000000000000) (35894868009 / 1000000000000), orderedInterval (-28559628111 / 1000000000000) (-28559547094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (331030846527147 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4562215878 / 1000000000000) (-4562215874 / 1000000000000), orderedInterval (38963207245 / 1000000000000) (38963207248 / 1000000000000)))) (orderedInterval (434238407 / 1000000000000) (434240897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (139972694973489 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10718143571 / 1000000000000) (-10718143514 / 1000000000000), orderedInterval (59391156529 / 1000000000000) (59391156586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (568981234015569 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27055400133 / 1000000000000) (27055498681 / 1000000000000), orderedInterval (-12790274925 / 1000000000000) (-12790176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (380053095419871 / 800000000000) 0 (IntervalRat.scale (765 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36424798298 / 1000000000000) (-36424798178 / 1000000000000), orderedInterval (-3608341200 / 1000000000000) (-3608341080 / 1000000000000)))) (orderedInterval (4567280170 / 1000000000000) (4567288322 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks0 :
    compactCertificate511.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate511.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate511_chunkChecks0_0
    compactCertificate511_chunkChecks0_1 compactCertificate511_chunkChecks0_2

theorem compactCertificate511_chunkChecks1_0 :
    compactCertificate511.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (765 / 2) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (439274361 / 1000000000000) (439274362 / 1000000000000), orderedInterval (40793713102 / 1000000000000) (40793713103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (225398215028853 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9937663878 / 1000000000000) (-9937663837 / 1000000000000), orderedInterval (46501869786 / 1000000000000) (46501869827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (72889151641749 / 160000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27111391626 / 1000000000000) (-27111391625 / 1000000000000), orderedInterval (-25707869886 / 1000000000000) (-25707869885 / 1000000000000)))) (orderedInterval (14691669686 / 1000000000000) (14691669718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (65770636994271 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85150214874 / 1000000000000) (85150214875 / 1000000000000), orderedInterval (21681920994 / 1000000000000) (21681920996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (479691197190279 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11325551417 / 1000000000000) (-11325551416 / 1000000000000), orderedInterval (-30542939880 / 1000000000000) (-30542939879 / 1000000000000)))) (orderedInterval (3193802254 / 1000000000000) (3193802318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (353338364744127 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18417596849 / 1000000000000) (18417597597 / 1000000000000), orderedInterval (-33219876255 / 1000000000000) (-33219875507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (605451310448571 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13278228219 / 1000000000000) (-13278228218 / 1000000000000), orderedInterval (-25776349918 / 1000000000000) (-25776349917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (445972694973489 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27536099890 / 1000000000000) (-27536058145 / 1000000000000), orderedInterval (19614289832 / 1000000000000) (19614331577 / 1000000000000)))) (orderedInterval (2263953606 / 1000000000000) (2263955114 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks1_1 :
    compactCertificate511.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (684236801114847 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27282246869 / 1000000000000) (27282250952 / 1000000000000), orderedInterval (58930614 / 1000000000000) (58934698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (395044301313063 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35114368582 / 1000000000000) (-35114368555 / 1000000000000), orderedInterval (-7460605926 / 1000000000000) (-7460605899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (701013045045267 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14024338843 / 1000000000000) (-14024338842 / 1000000000000), orderedInterval (-23010077788 / 1000000000000) (-23010077787 / 1000000000000)))) (orderedInterval (-8230588856 / 1000000000000) (-8230586917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (654977319701823 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12098594101 / 1000000000000) (12098594125 / 1000000000000), orderedInterval (-25131120581 / 1000000000000) (-25131120556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (467422720885359 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21947366453 / 1000000000000) (21947366454 / 1000000000000), orderedInterval (24636767124 / 1000000000000) (24636767125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (530007547115961 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12600234444 / 1000000000000) (-12600234443 / 1000000000000), orderedInterval (-28312850907 / 1000000000000) (-28312850906 / 1000000000000)))) (orderedInterval (4777987544 / 1000000000000) (4777987619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (441865036720809 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6617034614 / 1000000000000) (6617034615 / 1000000000000), orderedInterval (33292962072 / 1000000000000) (33292962073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (390401160364989 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34820180619 / 1000000000000) (-34820170748 / 1000000000000), orderedInterval (9632525076 / 1000000000000) (9632534947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (113153472889911 / 160000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27212492387 / 1000000000000) (-27212492382 / 1000000000000), orderedInterval (-12616663372 / 1000000000000) (-12616663368 / 1000000000000)))) (orderedInterval (-745391133 / 1000000000000) (-745390358 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks1_2 :
    compactCertificate511.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (312988460954517 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25315245172 / 1000000000000) (25315251955 / 1000000000000), orderedInterval (-31438432748 / 1000000000000) (-31438425965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (265323784603437 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-23608217504 / 1000000000000) (-23608214576 / 1000000000000), orderedInterval (36943295499 / 1000000000000) (36943298427 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (166027305026511 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45805577804 / 1000000000000) (45805577805 / 1000000000000), orderedInterval (31024644912 / 1000000000000) (31024644913 / 1000000000000)))) (orderedInterval (3876539266 / 1000000000000) (3876540609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (89290036825137 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48683032091 / 1000000000000) (-48682999276 / 1000000000000), orderedInterval (57957227685 / 1000000000000) (57957260500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (242439819366411 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35894786992 / 1000000000000) (35894868009 / 1000000000000), orderedInterval (-28559628111 / 1000000000000) (-28559547094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (331030846527147 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4562215878 / 1000000000000) (-4562215874 / 1000000000000), orderedInterval (38963207245 / 1000000000000) (38963207248 / 1000000000000)))) (orderedInterval (-3029293648 / 1000000000000) (-3029291973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (139972694973489 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10718143571 / 1000000000000) (-10718143514 / 1000000000000), orderedInterval (59391156529 / 1000000000000) (59391156586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (568981234015569 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27055400133 / 1000000000000) (27055498681 / 1000000000000), orderedInterval (-12790274925 / 1000000000000) (-12790176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (380053095419871 / 800000000000) 1 (IntervalRat.scale (765 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36424798298 / 1000000000000) (-36424798178 / 1000000000000), orderedInterval (-3608341200 / 1000000000000) (-3608341080 / 1000000000000)))) (orderedInterval (2940552056 / 1000000000000) (2940567150 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks1 :
    compactCertificate511.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate511.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate511_chunkChecks1_0
    compactCertificate511_chunkChecks1_1 compactCertificate511_chunkChecks1_2

theorem compactCertificate511_chunkChecks2_0 :
    compactCertificate511.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (765 / 2) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (439274361 / 1000000000000) (439274362 / 1000000000000), orderedInterval (40793713102 / 1000000000000) (40793713103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (225398215028853 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9937663878 / 1000000000000) (-9937663837 / 1000000000000), orderedInterval (46501869786 / 1000000000000) (46501869827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (72889151641749 / 160000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27111391626 / 1000000000000) (-27111391625 / 1000000000000), orderedInterval (-25707869886 / 1000000000000) (-25707869885 / 1000000000000)))) (orderedInterval (2094416771 / 1000000000000) (2094416807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (65770636994271 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85150214874 / 1000000000000) (85150214875 / 1000000000000), orderedInterval (21681920994 / 1000000000000) (21681920996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (479691197190279 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11325551417 / 1000000000000) (-11325551416 / 1000000000000), orderedInterval (-30542939880 / 1000000000000) (-30542939879 / 1000000000000)))) (orderedInterval (-2591367762 / 1000000000000) (-2591367683 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (353338364744127 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18417596849 / 1000000000000) (18417597597 / 1000000000000), orderedInterval (-33219876255 / 1000000000000) (-33219875507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (605451310448571 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13278228219 / 1000000000000) (-13278228218 / 1000000000000), orderedInterval (-25776349918 / 1000000000000) (-25776349917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (445972694973489 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27536099890 / 1000000000000) (-27536058145 / 1000000000000), orderedInterval (19614289832 / 1000000000000) (19614331577 / 1000000000000)))) (orderedInterval (-195694006 / 1000000000000) (-195691793 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks2_1 :
    compactCertificate511.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (684236801114847 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27282246869 / 1000000000000) (27282250952 / 1000000000000), orderedInterval (58930614 / 1000000000000) (58934698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (395044301313063 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35114368582 / 1000000000000) (-35114368555 / 1000000000000), orderedInterval (-7460605926 / 1000000000000) (-7460605899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (701013045045267 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14024338843 / 1000000000000) (-14024338842 / 1000000000000), orderedInterval (-23010077788 / 1000000000000) (-23010077787 / 1000000000000)))) (orderedInterval (39059298984 / 1000000000000) (39059303293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (654977319701823 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12098594101 / 1000000000000) (12098594125 / 1000000000000), orderedInterval (-25131120581 / 1000000000000) (-25131120556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (467422720885359 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21947366453 / 1000000000000) (21947366454 / 1000000000000), orderedInterval (24636767124 / 1000000000000) (24636767125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (530007547115961 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12600234444 / 1000000000000) (-12600234443 / 1000000000000), orderedInterval (-28312850907 / 1000000000000) (-28312850906 / 1000000000000)))) (orderedInterval (-4045716706 / 1000000000000) (-4045716581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (441865036720809 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6617034614 / 1000000000000) (6617034615 / 1000000000000), orderedInterval (33292962072 / 1000000000000) (33292962073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (390401160364989 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34820180619 / 1000000000000) (-34820170748 / 1000000000000), orderedInterval (9632525076 / 1000000000000) (9632534947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (113153472889911 / 160000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27212492387 / 1000000000000) (-27212492382 / 1000000000000), orderedInterval (-12616663372 / 1000000000000) (-12616663368 / 1000000000000)))) (orderedInterval (-1019026598 / 1000000000000) (-1019025597 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks2_2 :
    compactCertificate511.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (312988460954517 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25315245172 / 1000000000000) (25315251955 / 1000000000000), orderedInterval (-31438432748 / 1000000000000) (-31438425965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (265323784603437 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-23608217504 / 1000000000000) (-23608214576 / 1000000000000), orderedInterval (36943295499 / 1000000000000) (36943298427 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (166027305026511 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45805577804 / 1000000000000) (45805577805 / 1000000000000), orderedInterval (31024644912 / 1000000000000) (31024644913 / 1000000000000)))) (orderedInterval (2780996005 / 1000000000000) (2780997353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (89290036825137 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48683032091 / 1000000000000) (-48682999276 / 1000000000000), orderedInterval (57957227685 / 1000000000000) (57957260500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (242439819366411 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35894786992 / 1000000000000) (35894868009 / 1000000000000), orderedInterval (-28559628111 / 1000000000000) (-28559547094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (331030846527147 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4562215878 / 1000000000000) (-4562215874 / 1000000000000), orderedInterval (38963207245 / 1000000000000) (38963207248 / 1000000000000)))) (orderedInterval (33371066 / 1000000000000) (33372317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (139972694973489 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10718143571 / 1000000000000) (-10718143514 / 1000000000000), orderedInterval (59391156529 / 1000000000000) (59391156586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (568981234015569 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27055400133 / 1000000000000) (27055498681 / 1000000000000), orderedInterval (-12790274925 / 1000000000000) (-12790176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (380053095419871 / 800000000000) 2 (IntervalRat.scale (765 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36424798298 / 1000000000000) (-36424798178 / 1000000000000), orderedInterval (-3608341200 / 1000000000000) (-3608341080 / 1000000000000)))) (orderedInterval (-2922019094 / 1000000000000) (-2921991064 / 1000000000000))) = true
  rfl'

theorem compactCertificate511_chunkChecks2 :
    compactCertificate511.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate511.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate511_chunkChecks2_0
    compactCertificate511_chunkChecks2_1 compactCertificate511_chunkChecks2_2

theorem compactCertificate511_chunkChecks3_0 :
    compactCertificate511.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (765 / 2) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (439274361 / 1000000000000) (439274362 / 1000000000000), orderedInterval (40793713102 / 1000000000000) (40793713103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (225398215028853 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9937663878 / 1000000000000) (-9937663837 / 1000000000000), orderedInterval (46501869786 / 1000000000000) (46501869827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (72889151641749 / 160000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27111391626 / 1000000000000) (-27111391625 / 1000000000000), orderedInterval (-25707869886 / 1000000000000) (-25707869885 / 1000000000000)))) (orderedInterval (-13799164552 / 1000000000000) (-13799164511 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (65770636994271 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85150214874 / 1000000000000) (85150214875 / 1000000000000), orderedInterval (21681920994 / 1000000000000) (21681920996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (479691197190279 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11325551417 / 1000000000000) (-11325551416 / 1000000000000), orderedInterval (-30542939880 / 1000000000000) (-30542939879 / 1000000000000)))) (orderedInterval (-8302203127 / 1000000000000) (-8302203014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (353338364744127 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18417596849 / 1000000000000) (18417597597 / 1000000000000), orderedInterval (-33219876255 / 1000000000000) (-33219875507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (605451310448571 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13278228219 / 1000000000000) (-13278228218 / 1000000000000), orderedInterval (-25776349918 / 1000000000000) (-25776349917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (445972694973489 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27536099890 / 1000000000000) (-27536058145 / 1000000000000), orderedInterval (19614289832 / 1000000000000) (19614331577 / 1000000000000)))) (orderedInterval (-7625329591 / 1000000000000) (-7625326341 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate511_chunkChecks3_1 :
    compactCertificate511.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (684236801114847 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27282246869 / 1000000000000) (27282250952 / 1000000000000), orderedInterval (58930614 / 1000000000000) (58934698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (395044301313063 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35114368582 / 1000000000000) (-35114368555 / 1000000000000), orderedInterval (-7460605926 / 1000000000000) (-7460605899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (701013045045267 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14024338843 / 1000000000000) (-14024338842 / 1000000000000), orderedInterval (-23010077788 / 1000000000000) (-23010077787 / 1000000000000)))) (orderedInterval (40531827220 / 1000000000000) (40531836825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (654977319701823 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12098594101 / 1000000000000) (12098594125 / 1000000000000), orderedInterval (-25131120581 / 1000000000000) (-25131120556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (467422720885359 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21947366453 / 1000000000000) (21947366454 / 1000000000000), orderedInterval (24636767124 / 1000000000000) (24636767125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (530007547115961 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12600234444 / 1000000000000) (-12600234443 / 1000000000000), orderedInterval (-28312850907 / 1000000000000) (-28312850906 / 1000000000000)))) (orderedInterval (-13486708797 / 1000000000000) (-13486708585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (441865036720809 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6617034614 / 1000000000000) (6617034615 / 1000000000000), orderedInterval (33292962072 / 1000000000000) (33292962073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (390401160364989 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34820180619 / 1000000000000) (-34820170748 / 1000000000000), orderedInterval (9632525076 / 1000000000000) (9632534947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (113153472889911 / 160000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27212492387 / 1000000000000) (-27212492382 / 1000000000000), orderedInterval (-12616663372 / 1000000000000) (-12616663368 / 1000000000000)))) (orderedInterval (2031562143 / 1000000000000) (2031563441 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate511_chunkChecks3_2 :
    compactCertificate511.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (312988460954517 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25315245172 / 1000000000000) (25315251955 / 1000000000000), orderedInterval (-31438432748 / 1000000000000) (-31438425965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (265323784603437 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-23608217504 / 1000000000000) (-23608214576 / 1000000000000), orderedInterval (36943295499 / 1000000000000) (36943298427 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (166027305026511 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45805577804 / 1000000000000) (45805577805 / 1000000000000), orderedInterval (31024644912 / 1000000000000) (31024644913 / 1000000000000)))) (orderedInterval (-4184605010 / 1000000000000) (-4184603655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (89290036825137 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48683032091 / 1000000000000) (-48682999276 / 1000000000000), orderedInterval (57957227685 / 1000000000000) (57957260500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (242439819366411 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35894786992 / 1000000000000) (35894868009 / 1000000000000), orderedInterval (-28559628111 / 1000000000000) (-28559547094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (331030846527147 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4562215878 / 1000000000000) (-4562215874 / 1000000000000), orderedInterval (38963207245 / 1000000000000) (38963207248 / 1000000000000)))) (orderedInterval (3484707053 / 1000000000000) (3484708029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (139972694973489 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10718143571 / 1000000000000) (-10718143514 / 1000000000000), orderedInterval (59391156529 / 1000000000000) (59391156586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (568981234015569 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27055400133 / 1000000000000) (27055498681 / 1000000000000), orderedInterval (-12790274925 / 1000000000000) (-12790176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (380053095419871 / 800000000000) 3 (IntervalRat.scale (765 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36424798298 / 1000000000000) (-36424798178 / 1000000000000), orderedInterval (-3608341200 / 1000000000000) (-3608341080 / 1000000000000)))) (orderedInterval (-8017045930 / 1000000000000) (-8016993904 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate511_chunkChecks3 :
    compactCertificate511.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate511.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate511_chunkChecks3_0
    compactCertificate511_chunkChecks3_1 compactCertificate511_chunkChecks3_2

theorem compactCertificate511_chunkChecks4_0 :
    compactCertificate511.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (765 / 2) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (439274361 / 1000000000000) (439274362 / 1000000000000), orderedInterval (40793713102 / 1000000000000) (40793713103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (225398215028853 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9937663878 / 1000000000000) (-9937663837 / 1000000000000), orderedInterval (46501869786 / 1000000000000) (46501869827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (72889151641749 / 160000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27111391626 / 1000000000000) (-27111391625 / 1000000000000), orderedInterval (-25707869886 / 1000000000000) (-25707869885 / 1000000000000)))) (orderedInterval (-2982058429 / 1000000000000) (-2982058381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (65770636994271 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85150214874 / 1000000000000) (85150214875 / 1000000000000), orderedInterval (21681920994 / 1000000000000) (21681920996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (176669182371987 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53173262973 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984136 / 1000000000000) (-7560983623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (479691197190279 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11325551417 / 1000000000000) (-11325551416 / 1000000000000), orderedInterval (-30542939880 / 1000000000000) (-30542939879 / 1000000000000)))) (orderedInterval (5119271707 / 1000000000000) (5119271876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (353338364744127 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18417596849 / 1000000000000) (18417597597 / 1000000000000), orderedInterval (-33219876255 / 1000000000000) (-33219875507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (605451310448571 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13278228219 / 1000000000000) (-13278228218 / 1000000000000), orderedInterval (-25776349918 / 1000000000000) (-25776349917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (445972694973489 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27536099890 / 1000000000000) (-27536058145 / 1000000000000), orderedInterval (19614289832 / 1000000000000) (19614331577 / 1000000000000)))) (orderedInterval (3314168292 / 1000000000000) (3314173084 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate511_chunkChecks4_1 :
    compactCertificate511.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (684236801114847 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27282246869 / 1000000000000) (27282250952 / 1000000000000), orderedInterval (58930614 / 1000000000000) (58934698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (395044301313063 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35114368582 / 1000000000000) (-35114368555 / 1000000000000), orderedInterval (-7460605926 / 1000000000000) (-7460605899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (701013045045267 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14024338843 / 1000000000000) (-14024338842 / 1000000000000), orderedInterval (-23010077788 / 1000000000000) (-23010077787 / 1000000000000)))) (orderedInterval (-183543569933 / 1000000000000) (-183543548466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (654977319701823 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12098594101 / 1000000000000) (12098594125 / 1000000000000), orderedInterval (-25131120581 / 1000000000000) (-25131120556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (467422720885359 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21947366453 / 1000000000000) (21947366454 / 1000000000000), orderedInterval (24636767124 / 1000000000000) (24636767125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (530007547115961 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12600234444 / 1000000000000) (-12600234443 / 1000000000000), orderedInterval (-28312850907 / 1000000000000) (-28312850906 / 1000000000000)))) (orderedInterval (7359157934 / 1000000000000) (7359158304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (441865036720809 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6617034614 / 1000000000000) (6617034615 / 1000000000000), orderedInterval (33292962072 / 1000000000000) (33292962073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (390401160364989 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34820180619 / 1000000000000) (-34820170748 / 1000000000000), orderedInterval (9632525076 / 1000000000000) (9632534947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (113153472889911 / 160000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27212492387 / 1000000000000) (-27212492382 / 1000000000000), orderedInterval (-12616663372 / 1000000000000) (-12616663368 / 1000000000000)))) (orderedInterval (-2541151259 / 1000000000000) (-2541149562 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate511_chunkChecks4_2 :
    compactCertificate511.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (312988460954517 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (25315245172 / 1000000000000) (25315251955 / 1000000000000), orderedInterval (-31438432748 / 1000000000000) (-31438425965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (265323784603437 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-23608217504 / 1000000000000) (-23608214576 / 1000000000000), orderedInterval (36943295499 / 1000000000000) (36943298427 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (166027305026511 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45805577804 / 1000000000000) (45805577805 / 1000000000000), orderedInterval (31024644912 / 1000000000000) (31024644913 / 1000000000000)))) (orderedInterval (-3523952612 / 1000000000000) (-3523951244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (89290036825137 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48683032091 / 1000000000000) (-48682999276 / 1000000000000), orderedInterval (57957227685 / 1000000000000) (57957260500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (242439819366411 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35894786992 / 1000000000000) (35894868009 / 1000000000000), orderedInterval (-28559628111 / 1000000000000) (-28559547094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (331030846527147 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4562215878 / 1000000000000) (-4562215874 / 1000000000000), orderedInterval (38963207245 / 1000000000000) (38963207248 / 1000000000000)))) (orderedInterval (146285917 / 1000000000000) (146286695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (139972694973489 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10718143571 / 1000000000000) (-10718143514 / 1000000000000), orderedInterval (59391156529 / 1000000000000) (59391156586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (568981234015569 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27055400133 / 1000000000000) (27055498681 / 1000000000000), orderedInterval (-12790274925 / 1000000000000) (-12790176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (380053095419871 / 800000000000) 4 (IntervalRat.scale (765 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36424798298 / 1000000000000) (-36424798178 / 1000000000000), orderedInterval (-3608341200 / 1000000000000) (-3608341080 / 1000000000000)))) (orderedInterval (-10025243242 / 1000000000000) (-10025146482 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate511_chunkChecks4 :
    compactCertificate511.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate511.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate511_chunkChecks4_0
    compactCertificate511_chunkChecks4_1 compactCertificate511_chunkChecks4_2

theorem compactCertificate511_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate511.chunkCheck r b = true :=
  compactCertificate511.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate511_chunkChecks0
    · exact compactCertificate511_chunkChecks1
    · exact compactCertificate511_chunkChecks2
    · exact compactCertificate511_chunkChecks3
    · exact compactCertificate511_chunkChecks4)

theorem compactCertificate511_coefficient0 :
    compactCertificate511.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate511_coefficient1 :
    compactCertificate511.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate511_coefficient2 :
    compactCertificate511.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate511_coefficient3 :
    compactCertificate511.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate511_coefficient4 :
    compactCertificate511.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate511_coefficients : ∀ r : Fin 5,
    compactCertificate511.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate511_coefficient0
  · exact compactCertificate511_coefficient1
  · exact compactCertificate511_coefficient2
  · exact compactCertificate511_coefficient3
  · exact compactCertificate511_coefficient4

theorem compactCertificate511_lower : (1 : ℚ) ≤ compactCertificate511.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate511, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate511_proves {t : ℝ} (ht : t ∈ compactCertificate511.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate511.proves compactCertificate511_states compactCertificate511_chunks
    compactCertificate511_coefficients compactCertificate511_lower ht

end Erdos232
