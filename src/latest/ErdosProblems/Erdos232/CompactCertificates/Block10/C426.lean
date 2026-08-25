/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate426 : CompactCertificate where
  left := 297
  right := 298
  center := 595 / 2
  grid := fun i =>
    match i.val with
    | 0 => 95
    | 1 => 70
    | 2 => 113
    | 3 => 20
    | 4 => 55
    | 5 => 149
    | 6 => 109
    | 7 => 187
    | 8 => 138
    | 9 => 212
    | 10 => 122
    | 11 => 217
    | 12 => 203
    | 13 => 145
    | 14 => 164
    | 15 => 137
    | 16 => 121
    | 17 => 175
    | 18 => 97
    | 19 => 82
    | 20 => 51
    | 21 => 28
    | 22 => 75
    | 23 => 102
    | 24 => 43
    | 25 => 176
    | _ => 118
  point := fun i =>
    match i.val with
    | 0 => 595 / 2
    | 1 => 175309722800219 / 800000000000
    | 2 => 56691562388027 / 160000000000
    | 3 => 51154939884433 / 800000000000
    | 4 => 137409364067101 / 800000000000
    | 5 => 373093153370217 / 800000000000
    | 6 => 274818728134321 / 800000000000
    | 7 => 470906574793333 / 800000000000
    | 8 => 346867651646047 / 800000000000
    | 9 => 532184178644881 / 800000000000
    | 10 => 307256678799049 / 800000000000
    | 11 => 545232368368541 / 800000000000
    | 12 => 509426804212529 / 800000000000
    | 13 => 363551005133057 / 800000000000
    | 14 => 412228092201303 / 800000000000
    | 15 => 343672806338407 / 800000000000
    | 16 => 303645346950547 / 800000000000
    | 17 => 88008256692153 / 160000000000
    | 18 => 243435469631291 / 800000000000
    | 19 => 206362943580451 / 800000000000
    | 20 => 129132348353953 / 800000000000
    | 21 => 69447806419551 / 800000000000
    | 22 => 188564303951653 / 800000000000
    | 23 => 257468436187781 / 800000000000
    | 24 => 108867651646047 / 800000000000
    | 25 => 442540959789887 / 800000000000
    | _ => 295596851993233 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (7658561749 / 1000000000000) (7658561768 / 1000000000000), orderedInterval (-45633565086 / 1000000000000) (-45633565068 / 1000000000000))
    | 1 => (orderedInterval (565687560 / 1000000000000) (565687563 / 1000000000000), orderedInterval (53894977835 / 1000000000000) (53894977837 / 1000000000000))
    | 2 => (orderedInterval (-4541190486 / 1000000000000) (-4541190485 / 1000000000000), orderedInterval (-42137448010 / 1000000000000) (-42137448009 / 1000000000000))
    | 3 => (orderedInterval (94571560918 / 1000000000000) (94571562759 / 1000000000000), orderedInterval (-32550188091 / 1000000000000) (-32550186251 / 1000000000000))
    | 4 => (orderedInterval (14543540218 / 1000000000000) (14543540359 / 1000000000000), orderedInterval (-59160117593 / 1000000000000) (-59160117452 / 1000000000000))
    | 5 => (orderedInterval (29961067057 / 1000000000000) (29961126165 / 1000000000000), orderedInterval (-21651489665 / 1000000000000) (-21651430557 / 1000000000000))
    | 6 => (orderedInterval (-41074304553 / 1000000000000) (-41074297840 / 1000000000000), orderedInterval (12948012590 / 1000000000000) (12948019302 / 1000000000000))
    | 7 => (orderedInterval (-30663594198 / 1000000000000) (-30663552792 / 1000000000000), orderedInterval (11911601961 / 1000000000000) (11911643367 / 1000000000000))
    | 8 => (orderedInterval (28273175346 / 1000000000000) (28273175347 / 1000000000000), orderedInterval (25830473388 / 1000000000000) (25830473389 / 1000000000000))
    | 9 => (orderedInterval (-68335855 / 1000000000000) (-68335854 / 1000000000000), orderedInterval (30935261973 / 1000000000000) (30935261974 / 1000000000000))
    | 10 => (orderedInterval (40710719288 / 1000000000000) (40710719574 / 1000000000000), orderedInterval (-493552896 / 1000000000000) (-493552610 / 1000000000000))
    | 11 => (orderedInterval (-17258846614 / 1000000000000) (-17258846613 / 1000000000000), orderedInterval (-25210775515 / 1000000000000) (-25210775514 / 1000000000000))
    | 12 => (orderedInterval (5492667472 / 1000000000000) (5492667474 / 1000000000000), orderedInterval (-31142292342 / 1000000000000) (-31142292340 / 1000000000000))
    | 13 => (orderedInterval (11312869539 / 1000000000000) (11312869586 / 1000000000000), orderedInterval (-35690339599 / 1000000000000) (-35690339552 / 1000000000000))
    | 14 => (orderedInterval (26385494287 / 1000000000000) (26385494288 / 1000000000000), orderedInterval (23196725508 / 1000000000000) (23196725509 / 1000000000000))
    | 15 => (orderedInterval (849855730 / 1000000000000) (849855731 / 1000000000000), orderedInterval (-38487342141 / 1000000000000) (-38487342140 / 1000000000000))
    | 16 => (orderedInterval (-8498970526 / 1000000000000) (-8498970525 / 1000000000000), orderedInterval (-40051764085 / 1000000000000) (-40051764084 / 1000000000000))
    | 17 => (orderedInterval (-29645496332 / 1000000000000) (-29645496330 / 1000000000000), orderedInterval (-16662156387 / 1000000000000) (-16662156386 / 1000000000000))
    | 18 => (orderedInterval (-15461981928 / 1000000000000) (-15461981927 / 1000000000000), orderedInterval (-43021633901 / 1000000000000) (-43021633900 / 1000000000000))
    | 19 => (orderedInterval (44887295597 / 1000000000000) (44887295598 / 1000000000000), orderedInterval (21198889338 / 1000000000000) (21198889339 / 1000000000000))
    | 20 => (orderedInterval (-57645113976 / 1000000000000) (-57645106384 / 1000000000000), orderedInterval (25098658652 / 1000000000000) (25098666244 / 1000000000000))
    | 21 => (orderedInterval (-31037084321 / 1000000000000) (-31037083069 / 1000000000000), orderedInterval (79992878942 / 1000000000000) (79992880194 / 1000000000000))
    | 22 => (orderedInterval (-39749123102 / 1000000000000) (-39749123101 / 1000000000000), orderedInterval (-33395815003 / 1000000000000) (-33395815002 / 1000000000000))
    | 23 => (orderedInterval (36522824036 / 1000000000000) (36522924320 / 1000000000000), orderedInterval (-25437274978 / 1000000000000) (-25437174695 / 1000000000000))
    | 24 => (orderedInterval (-66897301761 / 1000000000000) (-66897301035 / 1000000000000), orderedInterval (14488019587 / 1000000000000) (14488020313 / 1000000000000))
    | 25 => (orderedInterval (29274551189 / 1000000000000) (29274551190 / 1000000000000), orderedInterval (17115444282 / 1000000000000) (17115444283 / 1000000000000))
    | _ => (orderedInterval (-17183087959 / 1000000000000) (-17183087521 / 1000000000000), orderedInterval (37807946226 / 1000000000000) (37807946664 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (2774374639 / 1000000000000) (2774374668 / 1000000000000)
      | 1 => orderedInterval (-2624950079 / 1000000000000) (-2624945816 / 1000000000000)
      | 2 => orderedInterval (1629093509 / 1000000000000) (1629094804 / 1000000000000)
      | 3 => orderedInterval (575024952 / 1000000000000) (575025092 / 1000000000000)
      | 4 => orderedInterval (837091951 / 1000000000000) (837091991 / 1000000000000)
      | 5 => orderedInterval (-262860126 / 1000000000000) (-262860097 / 1000000000000)
      | 6 => orderedInterval (-1945017252 / 1000000000000) (-1945016930 / 1000000000000)
      | 7 => orderedInterval (-1324189426 / 1000000000000) (-1324181682 / 1000000000000)
      | _ => orderedInterval (437723628 / 1000000000000) (437723798 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-20662584116 / 1000000000000) (-20662584085 / 1000000000000)
      | 1 => orderedInterval (1241671112 / 1000000000000) (1241677748 / 1000000000000)
      | 2 => orderedInterval (182887592 / 1000000000000) (182890149 / 1000000000000)
      | 3 => orderedInterval (-20548716274 / 1000000000000) (-20548716001 / 1000000000000)
      | 4 => orderedInterval (-4155300423 / 1000000000000) (-4155300358 / 1000000000000)
      | 5 => orderedInterval (1493669348 / 1000000000000) (1493669390 / 1000000000000)
      | 6 => orderedInterval (6438905730 / 1000000000000) (6438905934 / 1000000000000)
      | 7 => orderedInterval (2278209388 / 1000000000000) (2278217742 / 1000000000000)
      | _ => orderedInterval (-11361130776 / 1000000000000) (-11361130555 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-2590992208 / 1000000000000) (-2590992173 / 1000000000000)
      | 1 => orderedInterval (5100350274 / 1000000000000) (5100360682 / 1000000000000)
      | 2 => orderedInterval (-5154644506 / 1000000000000) (-5154639446 / 1000000000000)
      | 3 => orderedInterval (7857291858 / 1000000000000) (7857292419 / 1000000000000)
      | 4 => orderedInterval (-1627300683 / 1000000000000) (-1627300576 / 1000000000000)
      | 5 => orderedInterval (1777614460 / 1000000000000) (1777614522 / 1000000000000)
      | 6 => orderedInterval (-145582322 / 1000000000000) (-145582182 / 1000000000000)
      | 7 => orderedInterval (2653204459 / 1000000000000) (2653213516 / 1000000000000)
      | _ => orderedInterval (3388361153 / 1000000000000) (3388361453 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (22072670325 / 1000000000000) (22072670364 / 1000000000000)
      | 1 => orderedInterval (-5534395947 / 1000000000000) (-5534379639 / 1000000000000)
      | 2 => orderedInterval (930628472 / 1000000000000) (930638476 / 1000000000000)
      | 3 => orderedInterval (104597251214 / 1000000000000) (104597252411 / 1000000000000)
      | 4 => orderedInterval (7131223380 / 1000000000000) (7131223558 / 1000000000000)
      | 5 => orderedInterval (-731156184 / 1000000000000) (-731156089 / 1000000000000)
      | 6 => orderedInterval (-6708770775 / 1000000000000) (-6708770670 / 1000000000000)
      | 7 => orderedInterval (-2817085757 / 1000000000000) (-2817075963 / 1000000000000)
      | _ => orderedInterval (22527723157 / 1000000000000) (22527723580 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (2352536927 / 1000000000000) (2352536972 / 1000000000000)
      | 1 => orderedInterval (-12768435797 / 1000000000000) (-12768410183 / 1000000000000)
      | 2 => orderedInterval (17571816913 / 1000000000000) (17571836727 / 1000000000000)
      | 3 => orderedInterval (-59597275443 / 1000000000000) (-59597272826 / 1000000000000)
      | 4 => orderedInterval (2493258833 / 1000000000000) (2493259138 / 1000000000000)
      | 5 => orderedInterval (-7533941788 / 1000000000000) (-7533941637 / 1000000000000)
      | 6 => orderedInterval (1152405407 / 1000000000000) (1152405492 / 1000000000000)
      | 7 => orderedInterval (-3455111367 / 1000000000000) (-3455100740 / 1000000000000)
      | _ => orderedInterval (-20983365316 / 1000000000000) (-20983364694 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (96291796 / 1000000000000) (96305828 / 1000000000000)
    | 1 => orderedInterval (-45092388419 / 1000000000000) (-45092370036 / 1000000000000)
    | 2 => orderedInterval (11258302485 / 1000000000000) (11258328215 / 1000000000000)
    | 3 => orderedInterval (141468087885 / 1000000000000) (141468126028 / 1000000000000)
    | _ => orderedInterval (-80768111631 / 1000000000000) (-80768051751 / 1000000000000)

theorem compactCertificate426_stateChecks0 :
    compactCertificate426.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (595 / 2)) (orderedInterval (7658561749 / 1000000000000) (7658561768 / 1000000000000), orderedInterval (-45633565086 / 1000000000000) (-45633565068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (175309722800219 / 800000000000)) (orderedInterval (565687560 / 1000000000000) (565687563 / 1000000000000), orderedInterval (53894977835 / 1000000000000) (53894977837 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (56691562388027 / 160000000000)) (orderedInterval (-4541190486 / 1000000000000) (-4541190485 / 1000000000000), orderedInterval (-42137448010 / 1000000000000) (-42137448009 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_stateChecks1 :
    compactCertificate426.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (51154939884433 / 800000000000)) (orderedInterval (94571560918 / 1000000000000) (94571562759 / 1000000000000), orderedInterval (-32550188091 / 1000000000000) (-32550186251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (137409364067101 / 800000000000)) (orderedInterval (14543540218 / 1000000000000) (14543540359 / 1000000000000), orderedInterval (-59160117593 / 1000000000000) (-59160117452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (373093153370217 / 800000000000)) (orderedInterval (29961067057 / 1000000000000) (29961126165 / 1000000000000), orderedInterval (-21651489665 / 1000000000000) (-21651430557 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_stateChecks2 :
    compactCertificate426.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (274818728134321 / 800000000000)) (orderedInterval (-41074304553 / 1000000000000) (-41074297840 / 1000000000000), orderedInterval (12948012590 / 1000000000000) (12948019302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (470906574793333 / 800000000000)) (orderedInterval (-30663594198 / 1000000000000) (-30663552792 / 1000000000000), orderedInterval (11911601961 / 1000000000000) (11911643367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (346867651646047 / 800000000000)) (orderedInterval (28273175346 / 1000000000000) (28273175347 / 1000000000000), orderedInterval (25830473388 / 1000000000000) (25830473389 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_stateChecks3 :
    compactCertificate426.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (532184178644881 / 800000000000)) (orderedInterval (-68335855 / 1000000000000) (-68335854 / 1000000000000), orderedInterval (30935261973 / 1000000000000) (30935261974 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (307256678799049 / 800000000000)) (orderedInterval (40710719288 / 1000000000000) (40710719574 / 1000000000000), orderedInterval (-493552896 / 1000000000000) (-493552610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (545232368368541 / 800000000000)) (orderedInterval (-17258846614 / 1000000000000) (-17258846613 / 1000000000000), orderedInterval (-25210775515 / 1000000000000) (-25210775514 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_stateChecks4 :
    compactCertificate426.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (509426804212529 / 800000000000)) (orderedInterval (5492667472 / 1000000000000) (5492667474 / 1000000000000), orderedInterval (-31142292342 / 1000000000000) (-31142292340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (363551005133057 / 800000000000)) (orderedInterval (11312869539 / 1000000000000) (11312869586 / 1000000000000), orderedInterval (-35690339599 / 1000000000000) (-35690339552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (412228092201303 / 800000000000)) (orderedInterval (26385494287 / 1000000000000) (26385494288 / 1000000000000), orderedInterval (23196725508 / 1000000000000) (23196725509 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_stateChecks5 :
    compactCertificate426.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (343672806338407 / 800000000000)) (orderedInterval (849855730 / 1000000000000) (849855731 / 1000000000000), orderedInterval (-38487342141 / 1000000000000) (-38487342140 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (303645346950547 / 800000000000)) (orderedInterval (-8498970526 / 1000000000000) (-8498970525 / 1000000000000), orderedInterval (-40051764085 / 1000000000000) (-40051764084 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (88008256692153 / 160000000000)) (orderedInterval (-29645496332 / 1000000000000) (-29645496330 / 1000000000000), orderedInterval (-16662156387 / 1000000000000) (-16662156386 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_stateChecks6 :
    compactCertificate426.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (243435469631291 / 800000000000)) (orderedInterval (-15461981928 / 1000000000000) (-15461981927 / 1000000000000), orderedInterval (-43021633901 / 1000000000000) (-43021633900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (206362943580451 / 800000000000)) (orderedInterval (44887295597 / 1000000000000) (44887295598 / 1000000000000), orderedInterval (21198889338 / 1000000000000) (21198889339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (129132348353953 / 800000000000)) (orderedInterval (-57645113976 / 1000000000000) (-57645106384 / 1000000000000), orderedInterval (25098658652 / 1000000000000) (25098666244 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_stateChecks7 :
    compactCertificate426.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (69447806419551 / 800000000000)) (orderedInterval (-31037084321 / 1000000000000) (-31037083069 / 1000000000000), orderedInterval (79992878942 / 1000000000000) (79992880194 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (188564303951653 / 800000000000)) (orderedInterval (-39749123102 / 1000000000000) (-39749123101 / 1000000000000), orderedInterval (-33395815003 / 1000000000000) (-33395815002 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (257468436187781 / 800000000000)) (orderedInterval (36522824036 / 1000000000000) (36522924320 / 1000000000000), orderedInterval (-25437274978 / 1000000000000) (-25437174695 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_stateChecks8 :
    compactCertificate426.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (108867651646047 / 800000000000)) (orderedInterval (-66897301761 / 1000000000000) (-66897301035 / 1000000000000), orderedInterval (14488019587 / 1000000000000) (14488020313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (442540959789887 / 800000000000)) (orderedInterval (29274551189 / 1000000000000) (29274551190 / 1000000000000), orderedInterval (17115444282 / 1000000000000) (17115444283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (295596851993233 / 800000000000)) (orderedInterval (-17183087959 / 1000000000000) (-17183087521 / 1000000000000), orderedInterval (37807946226 / 1000000000000) (37807946664 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_states : ∀ j,
    BesselStateValid (compactCertificate426.point j) (compactCertificate426.state j) :=
  compactCertificate426.statesValid_of_checks3 compactCertificate426_stateChecks0
    compactCertificate426_stateChecks1 compactCertificate426_stateChecks2
    compactCertificate426_stateChecks3 compactCertificate426_stateChecks4
    compactCertificate426_stateChecks5 compactCertificate426_stateChecks6
    compactCertificate426_stateChecks7 compactCertificate426_stateChecks8

theorem compactCertificate426_chunkChecks0_0 :
    compactCertificate426.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (595 / 2) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7658561749 / 1000000000000) (7658561768 / 1000000000000), orderedInterval (-45633565086 / 1000000000000) (-45633565068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (175309722800219 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (565687560 / 1000000000000) (565687563 / 1000000000000), orderedInterval (53894977835 / 1000000000000) (53894977837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (56691562388027 / 160000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4541190486 / 1000000000000) (-4541190485 / 1000000000000), orderedInterval (-42137448010 / 1000000000000) (-42137448009 / 1000000000000)))) (orderedInterval (2774374639 / 1000000000000) (2774374668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (51154939884433 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94571560918 / 1000000000000) (94571562759 / 1000000000000), orderedInterval (-32550188091 / 1000000000000) (-32550186251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (137409364067101 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14543540218 / 1000000000000) (14543540359 / 1000000000000), orderedInterval (-59160117593 / 1000000000000) (-59160117452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (373093153370217 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29961067057 / 1000000000000) (29961126165 / 1000000000000), orderedInterval (-21651489665 / 1000000000000) (-21651430557 / 1000000000000)))) (orderedInterval (-2624950079 / 1000000000000) (-2624945816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (274818728134321 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41074304553 / 1000000000000) (-41074297840 / 1000000000000), orderedInterval (12948012590 / 1000000000000) (12948019302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (470906574793333 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30663594198 / 1000000000000) (-30663552792 / 1000000000000), orderedInterval (11911601961 / 1000000000000) (11911643367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (346867651646047 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28273175346 / 1000000000000) (28273175347 / 1000000000000), orderedInterval (25830473388 / 1000000000000) (25830473389 / 1000000000000)))) (orderedInterval (1629093509 / 1000000000000) (1629094804 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks0_1 :
    compactCertificate426.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (532184178644881 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-68335855 / 1000000000000) (-68335854 / 1000000000000), orderedInterval (30935261973 / 1000000000000) (30935261974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (307256678799049 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40710719288 / 1000000000000) (40710719574 / 1000000000000), orderedInterval (-493552896 / 1000000000000) (-493552610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (545232368368541 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17258846614 / 1000000000000) (-17258846613 / 1000000000000), orderedInterval (-25210775515 / 1000000000000) (-25210775514 / 1000000000000)))) (orderedInterval (575024952 / 1000000000000) (575025092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (509426804212529 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5492667472 / 1000000000000) (5492667474 / 1000000000000), orderedInterval (-31142292342 / 1000000000000) (-31142292340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (363551005133057 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11312869539 / 1000000000000) (11312869586 / 1000000000000), orderedInterval (-35690339599 / 1000000000000) (-35690339552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (412228092201303 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385494287 / 1000000000000) (26385494288 / 1000000000000), orderedInterval (23196725508 / 1000000000000) (23196725509 / 1000000000000)))) (orderedInterval (837091951 / 1000000000000) (837091991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (343672806338407 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (849855730 / 1000000000000) (849855731 / 1000000000000), orderedInterval (-38487342141 / 1000000000000) (-38487342140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (303645346950547 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8498970526 / 1000000000000) (-8498970525 / 1000000000000), orderedInterval (-40051764085 / 1000000000000) (-40051764084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (88008256692153 / 160000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29645496332 / 1000000000000) (-29645496330 / 1000000000000), orderedInterval (-16662156387 / 1000000000000) (-16662156386 / 1000000000000)))) (orderedInterval (-262860126 / 1000000000000) (-262860097 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks0_2 :
    compactCertificate426.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (243435469631291 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15461981928 / 1000000000000) (-15461981927 / 1000000000000), orderedInterval (-43021633901 / 1000000000000) (-43021633900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (206362943580451 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44887295597 / 1000000000000) (44887295598 / 1000000000000), orderedInterval (21198889338 / 1000000000000) (21198889339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (129132348353953 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57645113976 / 1000000000000) (-57645106384 / 1000000000000), orderedInterval (25098658652 / 1000000000000) (25098666244 / 1000000000000)))) (orderedInterval (-1945017252 / 1000000000000) (-1945016930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (69447806419551 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31037084321 / 1000000000000) (-31037083069 / 1000000000000), orderedInterval (79992878942 / 1000000000000) (79992880194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (188564303951653 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39749123102 / 1000000000000) (-39749123101 / 1000000000000), orderedInterval (-33395815003 / 1000000000000) (-33395815002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (257468436187781 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36522824036 / 1000000000000) (36522924320 / 1000000000000), orderedInterval (-25437274978 / 1000000000000) (-25437174695 / 1000000000000)))) (orderedInterval (-1324189426 / 1000000000000) (-1324181682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (108867651646047 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66897301761 / 1000000000000) (-66897301035 / 1000000000000), orderedInterval (14488019587 / 1000000000000) (14488020313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (442540959789887 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29274551189 / 1000000000000) (29274551190 / 1000000000000), orderedInterval (17115444282 / 1000000000000) (17115444283 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (295596851993233 / 800000000000) 0 (IntervalRat.scale (595 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17183087959 / 1000000000000) (-17183087521 / 1000000000000), orderedInterval (37807946226 / 1000000000000) (37807946664 / 1000000000000)))) (orderedInterval (437723628 / 1000000000000) (437723798 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks0 :
    compactCertificate426.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate426.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate426_chunkChecks0_0
    compactCertificate426_chunkChecks0_1 compactCertificate426_chunkChecks0_2

theorem compactCertificate426_chunkChecks1_0 :
    compactCertificate426.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (595 / 2) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7658561749 / 1000000000000) (7658561768 / 1000000000000), orderedInterval (-45633565086 / 1000000000000) (-45633565068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (175309722800219 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (565687560 / 1000000000000) (565687563 / 1000000000000), orderedInterval (53894977835 / 1000000000000) (53894977837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (56691562388027 / 160000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4541190486 / 1000000000000) (-4541190485 / 1000000000000), orderedInterval (-42137448010 / 1000000000000) (-42137448009 / 1000000000000)))) (orderedInterval (-20662584116 / 1000000000000) (-20662584085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (51154939884433 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94571560918 / 1000000000000) (94571562759 / 1000000000000), orderedInterval (-32550188091 / 1000000000000) (-32550186251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (137409364067101 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14543540218 / 1000000000000) (14543540359 / 1000000000000), orderedInterval (-59160117593 / 1000000000000) (-59160117452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (373093153370217 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29961067057 / 1000000000000) (29961126165 / 1000000000000), orderedInterval (-21651489665 / 1000000000000) (-21651430557 / 1000000000000)))) (orderedInterval (1241671112 / 1000000000000) (1241677748 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (274818728134321 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41074304553 / 1000000000000) (-41074297840 / 1000000000000), orderedInterval (12948012590 / 1000000000000) (12948019302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (470906574793333 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30663594198 / 1000000000000) (-30663552792 / 1000000000000), orderedInterval (11911601961 / 1000000000000) (11911643367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (346867651646047 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28273175346 / 1000000000000) (28273175347 / 1000000000000), orderedInterval (25830473388 / 1000000000000) (25830473389 / 1000000000000)))) (orderedInterval (182887592 / 1000000000000) (182890149 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks1_1 :
    compactCertificate426.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (532184178644881 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-68335855 / 1000000000000) (-68335854 / 1000000000000), orderedInterval (30935261973 / 1000000000000) (30935261974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (307256678799049 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40710719288 / 1000000000000) (40710719574 / 1000000000000), orderedInterval (-493552896 / 1000000000000) (-493552610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (545232368368541 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17258846614 / 1000000000000) (-17258846613 / 1000000000000), orderedInterval (-25210775515 / 1000000000000) (-25210775514 / 1000000000000)))) (orderedInterval (-20548716274 / 1000000000000) (-20548716001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (509426804212529 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5492667472 / 1000000000000) (5492667474 / 1000000000000), orderedInterval (-31142292342 / 1000000000000) (-31142292340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (363551005133057 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11312869539 / 1000000000000) (11312869586 / 1000000000000), orderedInterval (-35690339599 / 1000000000000) (-35690339552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (412228092201303 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385494287 / 1000000000000) (26385494288 / 1000000000000), orderedInterval (23196725508 / 1000000000000) (23196725509 / 1000000000000)))) (orderedInterval (-4155300423 / 1000000000000) (-4155300358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (343672806338407 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (849855730 / 1000000000000) (849855731 / 1000000000000), orderedInterval (-38487342141 / 1000000000000) (-38487342140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (303645346950547 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8498970526 / 1000000000000) (-8498970525 / 1000000000000), orderedInterval (-40051764085 / 1000000000000) (-40051764084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (88008256692153 / 160000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29645496332 / 1000000000000) (-29645496330 / 1000000000000), orderedInterval (-16662156387 / 1000000000000) (-16662156386 / 1000000000000)))) (orderedInterval (1493669348 / 1000000000000) (1493669390 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks1_2 :
    compactCertificate426.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (243435469631291 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15461981928 / 1000000000000) (-15461981927 / 1000000000000), orderedInterval (-43021633901 / 1000000000000) (-43021633900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (206362943580451 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44887295597 / 1000000000000) (44887295598 / 1000000000000), orderedInterval (21198889338 / 1000000000000) (21198889339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (129132348353953 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57645113976 / 1000000000000) (-57645106384 / 1000000000000), orderedInterval (25098658652 / 1000000000000) (25098666244 / 1000000000000)))) (orderedInterval (6438905730 / 1000000000000) (6438905934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (69447806419551 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31037084321 / 1000000000000) (-31037083069 / 1000000000000), orderedInterval (79992878942 / 1000000000000) (79992880194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (188564303951653 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39749123102 / 1000000000000) (-39749123101 / 1000000000000), orderedInterval (-33395815003 / 1000000000000) (-33395815002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (257468436187781 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36522824036 / 1000000000000) (36522924320 / 1000000000000), orderedInterval (-25437274978 / 1000000000000) (-25437174695 / 1000000000000)))) (orderedInterval (2278209388 / 1000000000000) (2278217742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (108867651646047 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66897301761 / 1000000000000) (-66897301035 / 1000000000000), orderedInterval (14488019587 / 1000000000000) (14488020313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (442540959789887 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29274551189 / 1000000000000) (29274551190 / 1000000000000), orderedInterval (17115444282 / 1000000000000) (17115444283 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (295596851993233 / 800000000000) 1 (IntervalRat.scale (595 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17183087959 / 1000000000000) (-17183087521 / 1000000000000), orderedInterval (37807946226 / 1000000000000) (37807946664 / 1000000000000)))) (orderedInterval (-11361130776 / 1000000000000) (-11361130555 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks1 :
    compactCertificate426.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate426.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate426_chunkChecks1_0
    compactCertificate426_chunkChecks1_1 compactCertificate426_chunkChecks1_2

theorem compactCertificate426_chunkChecks2_0 :
    compactCertificate426.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (595 / 2) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7658561749 / 1000000000000) (7658561768 / 1000000000000), orderedInterval (-45633565086 / 1000000000000) (-45633565068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (175309722800219 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (565687560 / 1000000000000) (565687563 / 1000000000000), orderedInterval (53894977835 / 1000000000000) (53894977837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (56691562388027 / 160000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4541190486 / 1000000000000) (-4541190485 / 1000000000000), orderedInterval (-42137448010 / 1000000000000) (-42137448009 / 1000000000000)))) (orderedInterval (-2590992208 / 1000000000000) (-2590992173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (51154939884433 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94571560918 / 1000000000000) (94571562759 / 1000000000000), orderedInterval (-32550188091 / 1000000000000) (-32550186251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (137409364067101 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14543540218 / 1000000000000) (14543540359 / 1000000000000), orderedInterval (-59160117593 / 1000000000000) (-59160117452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (373093153370217 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29961067057 / 1000000000000) (29961126165 / 1000000000000), orderedInterval (-21651489665 / 1000000000000) (-21651430557 / 1000000000000)))) (orderedInterval (5100350274 / 1000000000000) (5100360682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (274818728134321 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41074304553 / 1000000000000) (-41074297840 / 1000000000000), orderedInterval (12948012590 / 1000000000000) (12948019302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (470906574793333 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30663594198 / 1000000000000) (-30663552792 / 1000000000000), orderedInterval (11911601961 / 1000000000000) (11911643367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (346867651646047 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28273175346 / 1000000000000) (28273175347 / 1000000000000), orderedInterval (25830473388 / 1000000000000) (25830473389 / 1000000000000)))) (orderedInterval (-5154644506 / 1000000000000) (-5154639446 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks2_1 :
    compactCertificate426.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (532184178644881 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-68335855 / 1000000000000) (-68335854 / 1000000000000), orderedInterval (30935261973 / 1000000000000) (30935261974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (307256678799049 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40710719288 / 1000000000000) (40710719574 / 1000000000000), orderedInterval (-493552896 / 1000000000000) (-493552610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (545232368368541 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17258846614 / 1000000000000) (-17258846613 / 1000000000000), orderedInterval (-25210775515 / 1000000000000) (-25210775514 / 1000000000000)))) (orderedInterval (7857291858 / 1000000000000) (7857292419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (509426804212529 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5492667472 / 1000000000000) (5492667474 / 1000000000000), orderedInterval (-31142292342 / 1000000000000) (-31142292340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (363551005133057 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11312869539 / 1000000000000) (11312869586 / 1000000000000), orderedInterval (-35690339599 / 1000000000000) (-35690339552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (412228092201303 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385494287 / 1000000000000) (26385494288 / 1000000000000), orderedInterval (23196725508 / 1000000000000) (23196725509 / 1000000000000)))) (orderedInterval (-1627300683 / 1000000000000) (-1627300576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (343672806338407 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (849855730 / 1000000000000) (849855731 / 1000000000000), orderedInterval (-38487342141 / 1000000000000) (-38487342140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (303645346950547 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8498970526 / 1000000000000) (-8498970525 / 1000000000000), orderedInterval (-40051764085 / 1000000000000) (-40051764084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (88008256692153 / 160000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29645496332 / 1000000000000) (-29645496330 / 1000000000000), orderedInterval (-16662156387 / 1000000000000) (-16662156386 / 1000000000000)))) (orderedInterval (1777614460 / 1000000000000) (1777614522 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks2_2 :
    compactCertificate426.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (243435469631291 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15461981928 / 1000000000000) (-15461981927 / 1000000000000), orderedInterval (-43021633901 / 1000000000000) (-43021633900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (206362943580451 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44887295597 / 1000000000000) (44887295598 / 1000000000000), orderedInterval (21198889338 / 1000000000000) (21198889339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (129132348353953 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57645113976 / 1000000000000) (-57645106384 / 1000000000000), orderedInterval (25098658652 / 1000000000000) (25098666244 / 1000000000000)))) (orderedInterval (-145582322 / 1000000000000) (-145582182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (69447806419551 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31037084321 / 1000000000000) (-31037083069 / 1000000000000), orderedInterval (79992878942 / 1000000000000) (79992880194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (188564303951653 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39749123102 / 1000000000000) (-39749123101 / 1000000000000), orderedInterval (-33395815003 / 1000000000000) (-33395815002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (257468436187781 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36522824036 / 1000000000000) (36522924320 / 1000000000000), orderedInterval (-25437274978 / 1000000000000) (-25437174695 / 1000000000000)))) (orderedInterval (2653204459 / 1000000000000) (2653213516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (108867651646047 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66897301761 / 1000000000000) (-66897301035 / 1000000000000), orderedInterval (14488019587 / 1000000000000) (14488020313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (442540959789887 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29274551189 / 1000000000000) (29274551190 / 1000000000000), orderedInterval (17115444282 / 1000000000000) (17115444283 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (295596851993233 / 800000000000) 2 (IntervalRat.scale (595 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17183087959 / 1000000000000) (-17183087521 / 1000000000000), orderedInterval (37807946226 / 1000000000000) (37807946664 / 1000000000000)))) (orderedInterval (3388361153 / 1000000000000) (3388361453 / 1000000000000))) = true
  rfl'

theorem compactCertificate426_chunkChecks2 :
    compactCertificate426.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate426.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate426_chunkChecks2_0
    compactCertificate426_chunkChecks2_1 compactCertificate426_chunkChecks2_2

theorem compactCertificate426_chunkChecks3_0 :
    compactCertificate426.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (595 / 2) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7658561749 / 1000000000000) (7658561768 / 1000000000000), orderedInterval (-45633565086 / 1000000000000) (-45633565068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (175309722800219 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (565687560 / 1000000000000) (565687563 / 1000000000000), orderedInterval (53894977835 / 1000000000000) (53894977837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (56691562388027 / 160000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4541190486 / 1000000000000) (-4541190485 / 1000000000000), orderedInterval (-42137448010 / 1000000000000) (-42137448009 / 1000000000000)))) (orderedInterval (22072670325 / 1000000000000) (22072670364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (51154939884433 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94571560918 / 1000000000000) (94571562759 / 1000000000000), orderedInterval (-32550188091 / 1000000000000) (-32550186251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (137409364067101 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14543540218 / 1000000000000) (14543540359 / 1000000000000), orderedInterval (-59160117593 / 1000000000000) (-59160117452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (373093153370217 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29961067057 / 1000000000000) (29961126165 / 1000000000000), orderedInterval (-21651489665 / 1000000000000) (-21651430557 / 1000000000000)))) (orderedInterval (-5534395947 / 1000000000000) (-5534379639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (274818728134321 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41074304553 / 1000000000000) (-41074297840 / 1000000000000), orderedInterval (12948012590 / 1000000000000) (12948019302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (470906574793333 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30663594198 / 1000000000000) (-30663552792 / 1000000000000), orderedInterval (11911601961 / 1000000000000) (11911643367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (346867651646047 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28273175346 / 1000000000000) (28273175347 / 1000000000000), orderedInterval (25830473388 / 1000000000000) (25830473389 / 1000000000000)))) (orderedInterval (930628472 / 1000000000000) (930638476 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate426_chunkChecks3_1 :
    compactCertificate426.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (532184178644881 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-68335855 / 1000000000000) (-68335854 / 1000000000000), orderedInterval (30935261973 / 1000000000000) (30935261974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (307256678799049 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40710719288 / 1000000000000) (40710719574 / 1000000000000), orderedInterval (-493552896 / 1000000000000) (-493552610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (545232368368541 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17258846614 / 1000000000000) (-17258846613 / 1000000000000), orderedInterval (-25210775515 / 1000000000000) (-25210775514 / 1000000000000)))) (orderedInterval (104597251214 / 1000000000000) (104597252411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (509426804212529 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5492667472 / 1000000000000) (5492667474 / 1000000000000), orderedInterval (-31142292342 / 1000000000000) (-31142292340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (363551005133057 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11312869539 / 1000000000000) (11312869586 / 1000000000000), orderedInterval (-35690339599 / 1000000000000) (-35690339552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (412228092201303 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385494287 / 1000000000000) (26385494288 / 1000000000000), orderedInterval (23196725508 / 1000000000000) (23196725509 / 1000000000000)))) (orderedInterval (7131223380 / 1000000000000) (7131223558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (343672806338407 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (849855730 / 1000000000000) (849855731 / 1000000000000), orderedInterval (-38487342141 / 1000000000000) (-38487342140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (303645346950547 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8498970526 / 1000000000000) (-8498970525 / 1000000000000), orderedInterval (-40051764085 / 1000000000000) (-40051764084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (88008256692153 / 160000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29645496332 / 1000000000000) (-29645496330 / 1000000000000), orderedInterval (-16662156387 / 1000000000000) (-16662156386 / 1000000000000)))) (orderedInterval (-731156184 / 1000000000000) (-731156089 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate426_chunkChecks3_2 :
    compactCertificate426.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (243435469631291 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15461981928 / 1000000000000) (-15461981927 / 1000000000000), orderedInterval (-43021633901 / 1000000000000) (-43021633900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (206362943580451 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44887295597 / 1000000000000) (44887295598 / 1000000000000), orderedInterval (21198889338 / 1000000000000) (21198889339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (129132348353953 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57645113976 / 1000000000000) (-57645106384 / 1000000000000), orderedInterval (25098658652 / 1000000000000) (25098666244 / 1000000000000)))) (orderedInterval (-6708770775 / 1000000000000) (-6708770670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (69447806419551 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31037084321 / 1000000000000) (-31037083069 / 1000000000000), orderedInterval (79992878942 / 1000000000000) (79992880194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (188564303951653 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39749123102 / 1000000000000) (-39749123101 / 1000000000000), orderedInterval (-33395815003 / 1000000000000) (-33395815002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (257468436187781 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36522824036 / 1000000000000) (36522924320 / 1000000000000), orderedInterval (-25437274978 / 1000000000000) (-25437174695 / 1000000000000)))) (orderedInterval (-2817085757 / 1000000000000) (-2817075963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (108867651646047 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66897301761 / 1000000000000) (-66897301035 / 1000000000000), orderedInterval (14488019587 / 1000000000000) (14488020313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (442540959789887 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29274551189 / 1000000000000) (29274551190 / 1000000000000), orderedInterval (17115444282 / 1000000000000) (17115444283 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (295596851993233 / 800000000000) 3 (IntervalRat.scale (595 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17183087959 / 1000000000000) (-17183087521 / 1000000000000), orderedInterval (37807946226 / 1000000000000) (37807946664 / 1000000000000)))) (orderedInterval (22527723157 / 1000000000000) (22527723580 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate426_chunkChecks3 :
    compactCertificate426.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate426.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate426_chunkChecks3_0
    compactCertificate426_chunkChecks3_1 compactCertificate426_chunkChecks3_2

theorem compactCertificate426_chunkChecks4_0 :
    compactCertificate426.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (595 / 2) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7658561749 / 1000000000000) (7658561768 / 1000000000000), orderedInterval (-45633565086 / 1000000000000) (-45633565068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (175309722800219 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (565687560 / 1000000000000) (565687563 / 1000000000000), orderedInterval (53894977835 / 1000000000000) (53894977837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (56691562388027 / 160000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4541190486 / 1000000000000) (-4541190485 / 1000000000000), orderedInterval (-42137448010 / 1000000000000) (-42137448009 / 1000000000000)))) (orderedInterval (2352536927 / 1000000000000) (2352536972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (51154939884433 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94571560918 / 1000000000000) (94571562759 / 1000000000000), orderedInterval (-32550188091 / 1000000000000) (-32550186251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (137409364067101 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14543540218 / 1000000000000) (14543540359 / 1000000000000), orderedInterval (-59160117593 / 1000000000000) (-59160117452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (373093153370217 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29961067057 / 1000000000000) (29961126165 / 1000000000000), orderedInterval (-21651489665 / 1000000000000) (-21651430557 / 1000000000000)))) (orderedInterval (-12768435797 / 1000000000000) (-12768410183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (274818728134321 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41074304553 / 1000000000000) (-41074297840 / 1000000000000), orderedInterval (12948012590 / 1000000000000) (12948019302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (470906574793333 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30663594198 / 1000000000000) (-30663552792 / 1000000000000), orderedInterval (11911601961 / 1000000000000) (11911643367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (346867651646047 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28273175346 / 1000000000000) (28273175347 / 1000000000000), orderedInterval (25830473388 / 1000000000000) (25830473389 / 1000000000000)))) (orderedInterval (17571816913 / 1000000000000) (17571836727 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate426_chunkChecks4_1 :
    compactCertificate426.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (532184178644881 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-68335855 / 1000000000000) (-68335854 / 1000000000000), orderedInterval (30935261973 / 1000000000000) (30935261974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (307256678799049 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40710719288 / 1000000000000) (40710719574 / 1000000000000), orderedInterval (-493552896 / 1000000000000) (-493552610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (545232368368541 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17258846614 / 1000000000000) (-17258846613 / 1000000000000), orderedInterval (-25210775515 / 1000000000000) (-25210775514 / 1000000000000)))) (orderedInterval (-59597275443 / 1000000000000) (-59597272826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (509426804212529 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5492667472 / 1000000000000) (5492667474 / 1000000000000), orderedInterval (-31142292342 / 1000000000000) (-31142292340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (363551005133057 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11312869539 / 1000000000000) (11312869586 / 1000000000000), orderedInterval (-35690339599 / 1000000000000) (-35690339552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (412228092201303 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385494287 / 1000000000000) (26385494288 / 1000000000000), orderedInterval (23196725508 / 1000000000000) (23196725509 / 1000000000000)))) (orderedInterval (2493258833 / 1000000000000) (2493259138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (343672806338407 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (849855730 / 1000000000000) (849855731 / 1000000000000), orderedInterval (-38487342141 / 1000000000000) (-38487342140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (303645346950547 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8498970526 / 1000000000000) (-8498970525 / 1000000000000), orderedInterval (-40051764085 / 1000000000000) (-40051764084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (88008256692153 / 160000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29645496332 / 1000000000000) (-29645496330 / 1000000000000), orderedInterval (-16662156387 / 1000000000000) (-16662156386 / 1000000000000)))) (orderedInterval (-7533941788 / 1000000000000) (-7533941637 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate426_chunkChecks4_2 :
    compactCertificate426.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (243435469631291 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15461981928 / 1000000000000) (-15461981927 / 1000000000000), orderedInterval (-43021633901 / 1000000000000) (-43021633900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (206362943580451 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44887295597 / 1000000000000) (44887295598 / 1000000000000), orderedInterval (21198889338 / 1000000000000) (21198889339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (129132348353953 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57645113976 / 1000000000000) (-57645106384 / 1000000000000), orderedInterval (25098658652 / 1000000000000) (25098666244 / 1000000000000)))) (orderedInterval (1152405407 / 1000000000000) (1152405492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (69447806419551 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31037084321 / 1000000000000) (-31037083069 / 1000000000000), orderedInterval (79992878942 / 1000000000000) (79992880194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (188564303951653 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39749123102 / 1000000000000) (-39749123101 / 1000000000000), orderedInterval (-33395815003 / 1000000000000) (-33395815002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (257468436187781 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36522824036 / 1000000000000) (36522924320 / 1000000000000), orderedInterval (-25437274978 / 1000000000000) (-25437174695 / 1000000000000)))) (orderedInterval (-3455111367 / 1000000000000) (-3455100740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (108867651646047 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-66897301761 / 1000000000000) (-66897301035 / 1000000000000), orderedInterval (14488019587 / 1000000000000) (14488020313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (442540959789887 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29274551189 / 1000000000000) (29274551190 / 1000000000000), orderedInterval (17115444282 / 1000000000000) (17115444283 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (295596851993233 / 800000000000) 4 (IntervalRat.scale (595 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17183087959 / 1000000000000) (-17183087521 / 1000000000000), orderedInterval (37807946226 / 1000000000000) (37807946664 / 1000000000000)))) (orderedInterval (-20983365316 / 1000000000000) (-20983364694 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate426_chunkChecks4 :
    compactCertificate426.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate426.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate426_chunkChecks4_0
    compactCertificate426_chunkChecks4_1 compactCertificate426_chunkChecks4_2

theorem compactCertificate426_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate426.chunkCheck r b = true :=
  compactCertificate426.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate426_chunkChecks0
    · exact compactCertificate426_chunkChecks1
    · exact compactCertificate426_chunkChecks2
    · exact compactCertificate426_chunkChecks3
    · exact compactCertificate426_chunkChecks4)

theorem compactCertificate426_coefficient0 :
    compactCertificate426.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate426_coefficient1 :
    compactCertificate426.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate426_coefficient2 :
    compactCertificate426.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate426_coefficient3 :
    compactCertificate426.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate426_coefficient4 :
    compactCertificate426.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate426_coefficients : ∀ r : Fin 5,
    compactCertificate426.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate426_coefficient0
  · exact compactCertificate426_coefficient1
  · exact compactCertificate426_coefficient2
  · exact compactCertificate426_coefficient3
  · exact compactCertificate426_coefficient4

theorem compactCertificate426_lower : (1 : ℚ) ≤ compactCertificate426.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate426, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate426_proves {t : ℝ} (ht : t ∈ compactCertificate426.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate426.proves compactCertificate426_states compactCertificate426_chunks
    compactCertificate426_coefficients compactCertificate426_lower ht

end Erdos232
