/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate312 : CompactCertificate where
  left := 185
  right := 186
  center := 371 / 2
  grid := fun i =>
    match i.val with
    | 0 => 59
    | 1 => 44
    | 2 => 70
    | 3 => 13
    | 4 => 34
    | 5 => 93
    | 6 => 68
    | 7 => 117
    | 8 => 86
    | 9 => 132
    | 10 => 76
    | 11 => 135
    | 12 => 126
    | 13 => 90
    | 14 => 102
    | 15 => 85
    | 16 => 75
    | 17 => 109
    | 18 => 60
    | 19 => 51
    | 20 => 32
    | 21 => 17
    | 22 => 47
    | 23 => 64
    | 24 => 27
    | 25 => 110
    | _ => 73
  point := fun i =>
    match i.val with
    | 0 => 371 / 2
    | 1 => 546553841671271 / 4000000000000
    | 2 => 176744282739143 / 800000000000
    | 3 => 159483047874997 / 4000000000000
    | 4 => 428393899738609 / 4000000000000
    | 5 => 1163172772271853 / 4000000000000
    | 6 => 856787799477589 / 4000000000000
    | 7 => 1468120497885097 / 4000000000000
    | 8 => 1081410913955323 / 4000000000000
    | 9 => 1659162439304629 / 4000000000000
    | 10 => 957917880961741 / 4000000000000
    | 11 => 1699842089619569 / 4000000000000
    | 12 => 1588212977839061 / 4000000000000
    | 13 => 1133423721885413 / 4000000000000
    | 14 => 1285181699215827 / 4000000000000
    | 15 => 1071450513878563 / 4000000000000
    | 16 => 946659022845823 / 4000000000000
    | 17 => 274378682628477 / 800000000000
    | 18 => 758945875909319 / 4000000000000
    | 19 => 643366824103759 / 4000000000000
    | 20 => 402589086044677 / 4000000000000
    | 21 => 216513749425659 / 4000000000000
    | 22 => 587876947613977 / 4000000000000
    | 23 => 802695712820729 / 4000000000000
    | 24 => 339410913955323 / 4000000000000
    | 25 => 1379686521697883 / 4000000000000
    | _ => 921566656214197 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-46987361999 / 1000000000000) (-46987361998 / 1000000000000), orderedInterval (-34860444521 / 1000000000000) (-34860444520 / 1000000000000))
    | 1 => (orderedInterval (-49303130984 / 1000000000000) (-49303055745 / 1000000000000), orderedInterval (47385864852 / 1000000000000) (47385940090 / 1000000000000))
    | 2 => (orderedInterval (52230572018 / 1000000000000) (52230573599 / 1000000000000), orderedInterval (-12507767016 / 1000000000000) (-12507765436 / 1000000000000))
    | 3 => (orderedInterval (23575322665 / 1000000000000) (23575322829 / 1000000000000), orderedInterval (-124442506551 / 1000000000000) (-124442506387 / 1000000000000))
    | 4 => (orderedInterval (67577331239 / 1000000000000) (67577331240 / 1000000000000), orderedInterval (36799423398 / 1000000000000) (36799423399 / 1000000000000))
    | 5 => (orderedInterval (26030071128 / 1000000000000) (26030075709 / 1000000000000), orderedInterval (-38925206255 / 1000000000000) (-38925201674 / 1000000000000))
    | 6 => (orderedInterval (53234657862 / 1000000000000) (53234657865 / 1000000000000), orderedInterval (11631043732 / 1000000000000) (11631043735 / 1000000000000))
    | 7 => (orderedInterval (-10257006205 / 1000000000000) (-10257006204 / 1000000000000), orderedInterval (-40350759725 / 1000000000000) (-40350759724 / 1000000000000))
    | 8 => (orderedInterval (39771436286 / 1000000000000) (39771436287 / 1000000000000), orderedInterval (27729434572 / 1000000000000) (27729434573 / 1000000000000))
    | 9 => (orderedInterval (30331082427 / 1000000000000) (30331082428 / 1000000000000), orderedInterval (24759065859 / 1000000000000) (24759065860 / 1000000000000))
    | 10 => (orderedInterval (51441729599 / 1000000000000) (51441729633 / 1000000000000), orderedInterval (3369768440 / 1000000000000) (3369768474 / 1000000000000))
    | 11 => (orderedInterval (-38635635689 / 1000000000000) (-38635634999 / 1000000000000), orderedInterval (2359475787 / 1000000000000) (2359476477 / 1000000000000))
    | 12 => (orderedInterval (36449053092 / 1000000000000) (36449081905 / 1000000000000), orderedInterval (-16623785002 / 1000000000000) (-16623756189 / 1000000000000))
    | 13 => (orderedInterval (46689914922 / 1000000000000) (46689914932 / 1000000000000), orderedInterval (8088456307 / 1000000000000) (8088456316 / 1000000000000))
    | 14 => (orderedInterval (44412637685 / 1000000000000) (44412638078 / 1000000000000), orderedInterval (-3057565279 / 1000000000000) (-3057564886 / 1000000000000))
    | 15 => (orderedInterval (-48709261713 / 1000000000000) (-48709261516 / 1000000000000), orderedInterval (2108060751 / 1000000000000) (2108060948 / 1000000000000))
    | 16 => (orderedInterval (-50129885100 / 1000000000000) (-50129882767 / 1000000000000), orderedInterval (13408310895 / 1000000000000) (13408313229 / 1000000000000))
    | 17 => (orderedInterval (-41786221816 / 1000000000000) (-41786221811 / 1000000000000), orderedInterval (-10431386920 / 1000000000000) (-10431386915 / 1000000000000))
    | 18 => (orderedInterval (52035252722 / 1000000000000) (52035266661 / 1000000000000), orderedInterval (-25585288810 / 1000000000000) (-25585274870 / 1000000000000))
    | 19 => (orderedInterval (-62051242524 / 1000000000000) (-62051242520 / 1000000000000), orderedInterval (-10183850756 / 1000000000000) (-10183850752 / 1000000000000))
    | 20 => (orderedInterval (62321639274 / 1000000000000) (62321639275 / 1000000000000), orderedInterval (49099427093 / 1000000000000) (49099427094 / 1000000000000))
    | 21 => (orderedInterval (-108208543723 / 1000000000000) (-108208543714 / 1000000000000), orderedInterval (-6190467477 / 1000000000000) (-6190467469 / 1000000000000))
    | 22 => (orderedInterval (-6500463021 / 1000000000000) (-6500463020 / 1000000000000), orderedInterval (-65471562806 / 1000000000000) (-65471562804 / 1000000000000))
    | 23 => (orderedInterval (21766129692 / 1000000000000) (21766129693 / 1000000000000), orderedInterval (51894314285 / 1000000000000) (51894314286 / 1000000000000))
    | 24 => (orderedInterval (-62953303470 / 1000000000000) (-62953303469 / 1000000000000), orderedInterval (-59122902796 / 1000000000000) (-59122902795 / 1000000000000))
    | 25 => (orderedInterval (5632076905 / 1000000000000) (5632076906 / 1000000000000), orderedInterval (42582627569 / 1000000000000) (42582627570 / 1000000000000))
    | _ => (orderedInterval (-50669295810 / 1000000000000) (-50669293290 / 1000000000000), orderedInterval (14103661034 / 1000000000000) (14103663554 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16018605440 / 1000000000000) (-16018604633 / 1000000000000)
      | 1 => orderedInterval (361122067 / 1000000000000) (361122417 / 1000000000000)
      | 2 => orderedInterval (1277564250 / 1000000000000) (1277564261 / 1000000000000)
      | 3 => orderedInterval (-7070341572 / 1000000000000) (-7070341397 / 1000000000000)
      | 4 => orderedInterval (3532360216 / 1000000000000) (3532360762 / 1000000000000)
      | 5 => orderedInterval (1236395786 / 1000000000000) (1236395940 / 1000000000000)
      | 6 => orderedInterval (-2779050428 / 1000000000000) (-2779048152 / 1000000000000)
      | 7 => orderedInterval (477426932 / 1000000000000) (477426955 / 1000000000000)
      | _ => orderedInterval (8668939269 / 1000000000000) (8668939794 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14366378022 / 1000000000000) (-14366377380 / 1000000000000)
      | 1 => orderedInterval (5403802940 / 1000000000000) (5403803476 / 1000000000000)
      | 2 => orderedInterval (3439240264 / 1000000000000) (3439240283 / 1000000000000)
      | 3 => orderedInterval (-8746607354 / 1000000000000) (-8746606973 / 1000000000000)
      | 4 => orderedInterval (1837524936 / 1000000000000) (1837526091 / 1000000000000)
      | 5 => orderedInterval (-1437618886 / 1000000000000) (-1437618686 / 1000000000000)
      | 6 => orderedInterval (5551377909 / 1000000000000) (5551380232 / 1000000000000)
      | 7 => orderedInterval (-3092277090 / 1000000000000) (-3092277070 / 1000000000000)
      | _ => orderedInterval (-9894944994 / 1000000000000) (-9894944333 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14603287950 / 1000000000000) (14603288484 / 1000000000000)
      | 1 => orderedInterval (3707621018 / 1000000000000) (3707621856 / 1000000000000)
      | 2 => orderedInterval (-3298744382 / 1000000000000) (-3298744349 / 1000000000000)
      | 3 => orderedInterval (49466670995 / 1000000000000) (49466671843 / 1000000000000)
      | 4 => orderedInterval (-6622897603 / 1000000000000) (-6622895146 / 1000000000000)
      | 5 => orderedInterval (168458969 / 1000000000000) (168459232 / 1000000000000)
      | 6 => orderedInterval (5436768200 / 1000000000000) (5436770586 / 1000000000000)
      | 7 => orderedInterval (1706169016 / 1000000000000) (1706169037 / 1000000000000)
      | _ => orderedInterval (-12947247633 / 1000000000000) (-12947246793 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14801826280 / 1000000000000) (14801826740 / 1000000000000)
      | 1 => orderedInterval (-10951839035 / 1000000000000) (-10951837723 / 1000000000000)
      | 2 => orderedInterval (-11697173969 / 1000000000000) (-11697173910 / 1000000000000)
      | 3 => orderedInterval (44349825360 / 1000000000000) (44349827266 / 1000000000000)
      | 4 => orderedInterval (-5713842669 / 1000000000000) (-5713837440 / 1000000000000)
      | 5 => orderedInterval (3207316380 / 1000000000000) (3207316725 / 1000000000000)
      | 6 => orderedInterval (-5037833249 / 1000000000000) (-5037830810 / 1000000000000)
      | 7 => orderedInterval (4284283034 / 1000000000000) (4284283055 / 1000000000000)
      | _ => orderedInterval (27457606922 / 1000000000000) (27457607997 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-12751617818 / 1000000000000) (-12751617397 / 1000000000000)
      | 1 => orderedInterval (-10783092557 / 1000000000000) (-10783090495 / 1000000000000)
      | 2 => orderedInterval (9311392013 / 1000000000000) (9311392122 / 1000000000000)
      | 3 => orderedInterval (-275902711605 / 1000000000000) (-275902707289 / 1000000000000)
      | 4 => orderedInterval (8264545963 / 1000000000000) (8264557135 / 1000000000000)
      | 5 => orderedInterval (-7382193294 / 1000000000000) (-7382192832 / 1000000000000)
      | 6 => orderedInterval (-6891120473 / 1000000000000) (-6891117968 / 1000000000000)
      | 7 => orderedInterval (-2258189820 / 1000000000000) (-2258189798 / 1000000000000)
      | _ => orderedInterval (16828591095 / 1000000000000) (16828592495 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-10314188920 / 1000000000000) (-10314184053 / 1000000000000)
    | 1 => orderedInterval (-21305880297 / 1000000000000) (-21305874360 / 1000000000000)
    | 2 => orderedInterval (52220086530 / 1000000000000) (52220094750 / 1000000000000)
    | 3 => orderedInterval (60700169054 / 1000000000000) (60700181900 / 1000000000000)
    | _ => orderedInterval (-281564396496 / 1000000000000) (-281564374027 / 1000000000000)

theorem compactCertificate312_stateChecks0 :
    compactCertificate312.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (371 / 2)) (orderedInterval (-46987361999 / 1000000000000) (-46987361998 / 1000000000000), orderedInterval (-34860444521 / 1000000000000) (-34860444520 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (546553841671271 / 4000000000000)) (orderedInterval (-49303130984 / 1000000000000) (-49303055745 / 1000000000000), orderedInterval (47385864852 / 1000000000000) (47385940090 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176744282739143 / 800000000000)) (orderedInterval (52230572018 / 1000000000000) (52230573599 / 1000000000000), orderedInterval (-12507767016 / 1000000000000) (-12507765436 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_stateChecks1 :
    compactCertificate312.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (159483047874997 / 4000000000000)) (orderedInterval (23575322665 / 1000000000000) (23575322829 / 1000000000000), orderedInterval (-124442506551 / 1000000000000) (-124442506387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (428393899738609 / 4000000000000)) (orderedInterval (67577331239 / 1000000000000) (67577331240 / 1000000000000), orderedInterval (36799423398 / 1000000000000) (36799423399 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1163172772271853 / 4000000000000)) (orderedInterval (26030071128 / 1000000000000) (26030075709 / 1000000000000), orderedInterval (-38925206255 / 1000000000000) (-38925201674 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_stateChecks2 :
    compactCertificate312.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (856787799477589 / 4000000000000)) (orderedInterval (53234657862 / 1000000000000) (53234657865 / 1000000000000), orderedInterval (11631043732 / 1000000000000) (11631043735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1468120497885097 / 4000000000000)) (orderedInterval (-10257006205 / 1000000000000) (-10257006204 / 1000000000000), orderedInterval (-40350759725 / 1000000000000) (-40350759724 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1081410913955323 / 4000000000000)) (orderedInterval (39771436286 / 1000000000000) (39771436287 / 1000000000000), orderedInterval (27729434572 / 1000000000000) (27729434573 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_stateChecks3 :
    compactCertificate312.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1659162439304629 / 4000000000000)) (orderedInterval (30331082427 / 1000000000000) (30331082428 / 1000000000000), orderedInterval (24759065859 / 1000000000000) (24759065860 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (957917880961741 / 4000000000000)) (orderedInterval (51441729599 / 1000000000000) (51441729633 / 1000000000000), orderedInterval (3369768440 / 1000000000000) (3369768474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1699842089619569 / 4000000000000)) (orderedInterval (-38635635689 / 1000000000000) (-38635634999 / 1000000000000), orderedInterval (2359475787 / 1000000000000) (2359476477 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_stateChecks4 :
    compactCertificate312.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1588212977839061 / 4000000000000)) (orderedInterval (36449053092 / 1000000000000) (36449081905 / 1000000000000), orderedInterval (-16623785002 / 1000000000000) (-16623756189 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1133423721885413 / 4000000000000)) (orderedInterval (46689914922 / 1000000000000) (46689914932 / 1000000000000), orderedInterval (8088456307 / 1000000000000) (8088456316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1285181699215827 / 4000000000000)) (orderedInterval (44412637685 / 1000000000000) (44412638078 / 1000000000000), orderedInterval (-3057565279 / 1000000000000) (-3057564886 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_stateChecks5 :
    compactCertificate312.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1071450513878563 / 4000000000000)) (orderedInterval (-48709261713 / 1000000000000) (-48709261516 / 1000000000000), orderedInterval (2108060751 / 1000000000000) (2108060948 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (946659022845823 / 4000000000000)) (orderedInterval (-50129885100 / 1000000000000) (-50129882767 / 1000000000000), orderedInterval (13408310895 / 1000000000000) (13408313229 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (274378682628477 / 800000000000)) (orderedInterval (-41786221816 / 1000000000000) (-41786221811 / 1000000000000), orderedInterval (-10431386920 / 1000000000000) (-10431386915 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_stateChecks6 :
    compactCertificate312.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (758945875909319 / 4000000000000)) (orderedInterval (52035252722 / 1000000000000) (52035266661 / 1000000000000), orderedInterval (-25585288810 / 1000000000000) (-25585274870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (643366824103759 / 4000000000000)) (orderedInterval (-62051242524 / 1000000000000) (-62051242520 / 1000000000000), orderedInterval (-10183850756 / 1000000000000) (-10183850752 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (402589086044677 / 4000000000000)) (orderedInterval (62321639274 / 1000000000000) (62321639275 / 1000000000000), orderedInterval (49099427093 / 1000000000000) (49099427094 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_stateChecks7 :
    compactCertificate312.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (216513749425659 / 4000000000000)) (orderedInterval (-108208543723 / 1000000000000) (-108208543714 / 1000000000000), orderedInterval (-6190467477 / 1000000000000) (-6190467469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (587876947613977 / 4000000000000)) (orderedInterval (-6500463021 / 1000000000000) (-6500463020 / 1000000000000), orderedInterval (-65471562806 / 1000000000000) (-65471562804 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (802695712820729 / 4000000000000)) (orderedInterval (21766129692 / 1000000000000) (21766129693 / 1000000000000), orderedInterval (51894314285 / 1000000000000) (51894314286 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_stateChecks8 :
    compactCertificate312.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (339410913955323 / 4000000000000)) (orderedInterval (-62953303470 / 1000000000000) (-62953303469 / 1000000000000), orderedInterval (-59122902796 / 1000000000000) (-59122902795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1379686521697883 / 4000000000000)) (orderedInterval (5632076905 / 1000000000000) (5632076906 / 1000000000000), orderedInterval (42582627569 / 1000000000000) (42582627570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (921566656214197 / 4000000000000)) (orderedInterval (-50669295810 / 1000000000000) (-50669293290 / 1000000000000), orderedInterval (14103661034 / 1000000000000) (14103663554 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_states : ∀ j,
    BesselStateValid (compactCertificate312.point j) (compactCertificate312.state j) :=
  compactCertificate312.statesValid_of_checks3 compactCertificate312_stateChecks0
    compactCertificate312_stateChecks1 compactCertificate312_stateChecks2
    compactCertificate312_stateChecks3 compactCertificate312_stateChecks4
    compactCertificate312_stateChecks5 compactCertificate312_stateChecks6
    compactCertificate312_stateChecks7 compactCertificate312_stateChecks8

theorem compactCertificate312_chunkChecks0_0 :
    compactCertificate312.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (371 / 2) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46987361999 / 1000000000000) (-46987361998 / 1000000000000), orderedInterval (-34860444521 / 1000000000000) (-34860444520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (546553841671271 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49303130984 / 1000000000000) (-49303055745 / 1000000000000), orderedInterval (47385864852 / 1000000000000) (47385940090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (176744282739143 / 800000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52230572018 / 1000000000000) (52230573599 / 1000000000000), orderedInterval (-12507767016 / 1000000000000) (-12507765436 / 1000000000000)))) (orderedInterval (-16018605440 / 1000000000000) (-16018604633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (159483047874997 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23575322665 / 1000000000000) (23575322829 / 1000000000000), orderedInterval (-124442506551 / 1000000000000) (-124442506387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (428393899738609 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67577331239 / 1000000000000) (67577331240 / 1000000000000), orderedInterval (36799423398 / 1000000000000) (36799423399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1163172772271853 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26030071128 / 1000000000000) (26030075709 / 1000000000000), orderedInterval (-38925206255 / 1000000000000) (-38925201674 / 1000000000000)))) (orderedInterval (361122067 / 1000000000000) (361122417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (856787799477589 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53234657862 / 1000000000000) (53234657865 / 1000000000000), orderedInterval (11631043732 / 1000000000000) (11631043735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1468120497885097 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10257006205 / 1000000000000) (-10257006204 / 1000000000000), orderedInterval (-40350759725 / 1000000000000) (-40350759724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1081410913955323 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39771436286 / 1000000000000) (39771436287 / 1000000000000), orderedInterval (27729434572 / 1000000000000) (27729434573 / 1000000000000)))) (orderedInterval (1277564250 / 1000000000000) (1277564261 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks0_1 :
    compactCertificate312.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1659162439304629 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30331082427 / 1000000000000) (30331082428 / 1000000000000), orderedInterval (24759065859 / 1000000000000) (24759065860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (957917880961741 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51441729599 / 1000000000000) (51441729633 / 1000000000000), orderedInterval (3369768440 / 1000000000000) (3369768474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1699842089619569 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38635635689 / 1000000000000) (-38635634999 / 1000000000000), orderedInterval (2359475787 / 1000000000000) (2359476477 / 1000000000000)))) (orderedInterval (-7070341572 / 1000000000000) (-7070341397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1588212977839061 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36449053092 / 1000000000000) (36449081905 / 1000000000000), orderedInterval (-16623785002 / 1000000000000) (-16623756189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1133423721885413 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46689914922 / 1000000000000) (46689914932 / 1000000000000), orderedInterval (8088456307 / 1000000000000) (8088456316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1285181699215827 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44412637685 / 1000000000000) (44412638078 / 1000000000000), orderedInterval (-3057565279 / 1000000000000) (-3057564886 / 1000000000000)))) (orderedInterval (3532360216 / 1000000000000) (3532360762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1071450513878563 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48709261713 / 1000000000000) (-48709261516 / 1000000000000), orderedInterval (2108060751 / 1000000000000) (2108060948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (946659022845823 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50129885100 / 1000000000000) (-50129882767 / 1000000000000), orderedInterval (13408310895 / 1000000000000) (13408313229 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (274378682628477 / 800000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41786221816 / 1000000000000) (-41786221811 / 1000000000000), orderedInterval (-10431386920 / 1000000000000) (-10431386915 / 1000000000000)))) (orderedInterval (1236395786 / 1000000000000) (1236395940 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks0_2 :
    compactCertificate312.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (758945875909319 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52035252722 / 1000000000000) (52035266661 / 1000000000000), orderedInterval (-25585288810 / 1000000000000) (-25585274870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (643366824103759 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-62051242524 / 1000000000000) (-62051242520 / 1000000000000), orderedInterval (-10183850756 / 1000000000000) (-10183850752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (402589086044677 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62321639274 / 1000000000000) (62321639275 / 1000000000000), orderedInterval (49099427093 / 1000000000000) (49099427094 / 1000000000000)))) (orderedInterval (-2779050428 / 1000000000000) (-2779048152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (216513749425659 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-108208543723 / 1000000000000) (-108208543714 / 1000000000000), orderedInterval (-6190467477 / 1000000000000) (-6190467469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (587876947613977 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6500463021 / 1000000000000) (-6500463020 / 1000000000000), orderedInterval (-65471562806 / 1000000000000) (-65471562804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (802695712820729 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21766129692 / 1000000000000) (21766129693 / 1000000000000), orderedInterval (51894314285 / 1000000000000) (51894314286 / 1000000000000)))) (orderedInterval (477426932 / 1000000000000) (477426955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (339410913955323 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62953303470 / 1000000000000) (-62953303469 / 1000000000000), orderedInterval (-59122902796 / 1000000000000) (-59122902795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1379686521697883 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5632076905 / 1000000000000) (5632076906 / 1000000000000), orderedInterval (42582627569 / 1000000000000) (42582627570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (921566656214197 / 4000000000000) 0 (IntervalRat.scale (371 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50669295810 / 1000000000000) (-50669293290 / 1000000000000), orderedInterval (14103661034 / 1000000000000) (14103663554 / 1000000000000)))) (orderedInterval (8668939269 / 1000000000000) (8668939794 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks0 :
    compactCertificate312.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate312.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate312_chunkChecks0_0
    compactCertificate312_chunkChecks0_1 compactCertificate312_chunkChecks0_2

theorem compactCertificate312_chunkChecks1_0 :
    compactCertificate312.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (371 / 2) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46987361999 / 1000000000000) (-46987361998 / 1000000000000), orderedInterval (-34860444521 / 1000000000000) (-34860444520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (546553841671271 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49303130984 / 1000000000000) (-49303055745 / 1000000000000), orderedInterval (47385864852 / 1000000000000) (47385940090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (176744282739143 / 800000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52230572018 / 1000000000000) (52230573599 / 1000000000000), orderedInterval (-12507767016 / 1000000000000) (-12507765436 / 1000000000000)))) (orderedInterval (-14366378022 / 1000000000000) (-14366377380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (159483047874997 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23575322665 / 1000000000000) (23575322829 / 1000000000000), orderedInterval (-124442506551 / 1000000000000) (-124442506387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (428393899738609 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67577331239 / 1000000000000) (67577331240 / 1000000000000), orderedInterval (36799423398 / 1000000000000) (36799423399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1163172772271853 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26030071128 / 1000000000000) (26030075709 / 1000000000000), orderedInterval (-38925206255 / 1000000000000) (-38925201674 / 1000000000000)))) (orderedInterval (5403802940 / 1000000000000) (5403803476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (856787799477589 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53234657862 / 1000000000000) (53234657865 / 1000000000000), orderedInterval (11631043732 / 1000000000000) (11631043735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1468120497885097 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10257006205 / 1000000000000) (-10257006204 / 1000000000000), orderedInterval (-40350759725 / 1000000000000) (-40350759724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1081410913955323 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39771436286 / 1000000000000) (39771436287 / 1000000000000), orderedInterval (27729434572 / 1000000000000) (27729434573 / 1000000000000)))) (orderedInterval (3439240264 / 1000000000000) (3439240283 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks1_1 :
    compactCertificate312.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1659162439304629 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30331082427 / 1000000000000) (30331082428 / 1000000000000), orderedInterval (24759065859 / 1000000000000) (24759065860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (957917880961741 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51441729599 / 1000000000000) (51441729633 / 1000000000000), orderedInterval (3369768440 / 1000000000000) (3369768474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1699842089619569 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38635635689 / 1000000000000) (-38635634999 / 1000000000000), orderedInterval (2359475787 / 1000000000000) (2359476477 / 1000000000000)))) (orderedInterval (-8746607354 / 1000000000000) (-8746606973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1588212977839061 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36449053092 / 1000000000000) (36449081905 / 1000000000000), orderedInterval (-16623785002 / 1000000000000) (-16623756189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1133423721885413 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46689914922 / 1000000000000) (46689914932 / 1000000000000), orderedInterval (8088456307 / 1000000000000) (8088456316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1285181699215827 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44412637685 / 1000000000000) (44412638078 / 1000000000000), orderedInterval (-3057565279 / 1000000000000) (-3057564886 / 1000000000000)))) (orderedInterval (1837524936 / 1000000000000) (1837526091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1071450513878563 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48709261713 / 1000000000000) (-48709261516 / 1000000000000), orderedInterval (2108060751 / 1000000000000) (2108060948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (946659022845823 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50129885100 / 1000000000000) (-50129882767 / 1000000000000), orderedInterval (13408310895 / 1000000000000) (13408313229 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (274378682628477 / 800000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41786221816 / 1000000000000) (-41786221811 / 1000000000000), orderedInterval (-10431386920 / 1000000000000) (-10431386915 / 1000000000000)))) (orderedInterval (-1437618886 / 1000000000000) (-1437618686 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks1_2 :
    compactCertificate312.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (758945875909319 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52035252722 / 1000000000000) (52035266661 / 1000000000000), orderedInterval (-25585288810 / 1000000000000) (-25585274870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (643366824103759 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-62051242524 / 1000000000000) (-62051242520 / 1000000000000), orderedInterval (-10183850756 / 1000000000000) (-10183850752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (402589086044677 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62321639274 / 1000000000000) (62321639275 / 1000000000000), orderedInterval (49099427093 / 1000000000000) (49099427094 / 1000000000000)))) (orderedInterval (5551377909 / 1000000000000) (5551380232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (216513749425659 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-108208543723 / 1000000000000) (-108208543714 / 1000000000000), orderedInterval (-6190467477 / 1000000000000) (-6190467469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (587876947613977 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6500463021 / 1000000000000) (-6500463020 / 1000000000000), orderedInterval (-65471562806 / 1000000000000) (-65471562804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (802695712820729 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21766129692 / 1000000000000) (21766129693 / 1000000000000), orderedInterval (51894314285 / 1000000000000) (51894314286 / 1000000000000)))) (orderedInterval (-3092277090 / 1000000000000) (-3092277070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (339410913955323 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62953303470 / 1000000000000) (-62953303469 / 1000000000000), orderedInterval (-59122902796 / 1000000000000) (-59122902795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1379686521697883 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5632076905 / 1000000000000) (5632076906 / 1000000000000), orderedInterval (42582627569 / 1000000000000) (42582627570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (921566656214197 / 4000000000000) 1 (IntervalRat.scale (371 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50669295810 / 1000000000000) (-50669293290 / 1000000000000), orderedInterval (14103661034 / 1000000000000) (14103663554 / 1000000000000)))) (orderedInterval (-9894944994 / 1000000000000) (-9894944333 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks1 :
    compactCertificate312.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate312.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate312_chunkChecks1_0
    compactCertificate312_chunkChecks1_1 compactCertificate312_chunkChecks1_2

theorem compactCertificate312_chunkChecks2_0 :
    compactCertificate312.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (371 / 2) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46987361999 / 1000000000000) (-46987361998 / 1000000000000), orderedInterval (-34860444521 / 1000000000000) (-34860444520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (546553841671271 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49303130984 / 1000000000000) (-49303055745 / 1000000000000), orderedInterval (47385864852 / 1000000000000) (47385940090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (176744282739143 / 800000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52230572018 / 1000000000000) (52230573599 / 1000000000000), orderedInterval (-12507767016 / 1000000000000) (-12507765436 / 1000000000000)))) (orderedInterval (14603287950 / 1000000000000) (14603288484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (159483047874997 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23575322665 / 1000000000000) (23575322829 / 1000000000000), orderedInterval (-124442506551 / 1000000000000) (-124442506387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (428393899738609 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67577331239 / 1000000000000) (67577331240 / 1000000000000), orderedInterval (36799423398 / 1000000000000) (36799423399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1163172772271853 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26030071128 / 1000000000000) (26030075709 / 1000000000000), orderedInterval (-38925206255 / 1000000000000) (-38925201674 / 1000000000000)))) (orderedInterval (3707621018 / 1000000000000) (3707621856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (856787799477589 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53234657862 / 1000000000000) (53234657865 / 1000000000000), orderedInterval (11631043732 / 1000000000000) (11631043735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1468120497885097 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10257006205 / 1000000000000) (-10257006204 / 1000000000000), orderedInterval (-40350759725 / 1000000000000) (-40350759724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1081410913955323 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39771436286 / 1000000000000) (39771436287 / 1000000000000), orderedInterval (27729434572 / 1000000000000) (27729434573 / 1000000000000)))) (orderedInterval (-3298744382 / 1000000000000) (-3298744349 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks2_1 :
    compactCertificate312.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1659162439304629 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30331082427 / 1000000000000) (30331082428 / 1000000000000), orderedInterval (24759065859 / 1000000000000) (24759065860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (957917880961741 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51441729599 / 1000000000000) (51441729633 / 1000000000000), orderedInterval (3369768440 / 1000000000000) (3369768474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1699842089619569 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38635635689 / 1000000000000) (-38635634999 / 1000000000000), orderedInterval (2359475787 / 1000000000000) (2359476477 / 1000000000000)))) (orderedInterval (49466670995 / 1000000000000) (49466671843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1588212977839061 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36449053092 / 1000000000000) (36449081905 / 1000000000000), orderedInterval (-16623785002 / 1000000000000) (-16623756189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1133423721885413 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46689914922 / 1000000000000) (46689914932 / 1000000000000), orderedInterval (8088456307 / 1000000000000) (8088456316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1285181699215827 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44412637685 / 1000000000000) (44412638078 / 1000000000000), orderedInterval (-3057565279 / 1000000000000) (-3057564886 / 1000000000000)))) (orderedInterval (-6622897603 / 1000000000000) (-6622895146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1071450513878563 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48709261713 / 1000000000000) (-48709261516 / 1000000000000), orderedInterval (2108060751 / 1000000000000) (2108060948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (946659022845823 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50129885100 / 1000000000000) (-50129882767 / 1000000000000), orderedInterval (13408310895 / 1000000000000) (13408313229 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (274378682628477 / 800000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41786221816 / 1000000000000) (-41786221811 / 1000000000000), orderedInterval (-10431386920 / 1000000000000) (-10431386915 / 1000000000000)))) (orderedInterval (168458969 / 1000000000000) (168459232 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks2_2 :
    compactCertificate312.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (758945875909319 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52035252722 / 1000000000000) (52035266661 / 1000000000000), orderedInterval (-25585288810 / 1000000000000) (-25585274870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (643366824103759 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-62051242524 / 1000000000000) (-62051242520 / 1000000000000), orderedInterval (-10183850756 / 1000000000000) (-10183850752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (402589086044677 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62321639274 / 1000000000000) (62321639275 / 1000000000000), orderedInterval (49099427093 / 1000000000000) (49099427094 / 1000000000000)))) (orderedInterval (5436768200 / 1000000000000) (5436770586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (216513749425659 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-108208543723 / 1000000000000) (-108208543714 / 1000000000000), orderedInterval (-6190467477 / 1000000000000) (-6190467469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (587876947613977 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6500463021 / 1000000000000) (-6500463020 / 1000000000000), orderedInterval (-65471562806 / 1000000000000) (-65471562804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (802695712820729 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21766129692 / 1000000000000) (21766129693 / 1000000000000), orderedInterval (51894314285 / 1000000000000) (51894314286 / 1000000000000)))) (orderedInterval (1706169016 / 1000000000000) (1706169037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (339410913955323 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62953303470 / 1000000000000) (-62953303469 / 1000000000000), orderedInterval (-59122902796 / 1000000000000) (-59122902795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1379686521697883 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5632076905 / 1000000000000) (5632076906 / 1000000000000), orderedInterval (42582627569 / 1000000000000) (42582627570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (921566656214197 / 4000000000000) 2 (IntervalRat.scale (371 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50669295810 / 1000000000000) (-50669293290 / 1000000000000), orderedInterval (14103661034 / 1000000000000) (14103663554 / 1000000000000)))) (orderedInterval (-12947247633 / 1000000000000) (-12947246793 / 1000000000000))) = true
  rfl'

theorem compactCertificate312_chunkChecks2 :
    compactCertificate312.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate312.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate312_chunkChecks2_0
    compactCertificate312_chunkChecks2_1 compactCertificate312_chunkChecks2_2

theorem compactCertificate312_chunkChecks3_0 :
    compactCertificate312.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (371 / 2) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46987361999 / 1000000000000) (-46987361998 / 1000000000000), orderedInterval (-34860444521 / 1000000000000) (-34860444520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (546553841671271 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49303130984 / 1000000000000) (-49303055745 / 1000000000000), orderedInterval (47385864852 / 1000000000000) (47385940090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (176744282739143 / 800000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52230572018 / 1000000000000) (52230573599 / 1000000000000), orderedInterval (-12507767016 / 1000000000000) (-12507765436 / 1000000000000)))) (orderedInterval (14801826280 / 1000000000000) (14801826740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (159483047874997 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23575322665 / 1000000000000) (23575322829 / 1000000000000), orderedInterval (-124442506551 / 1000000000000) (-124442506387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (428393899738609 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67577331239 / 1000000000000) (67577331240 / 1000000000000), orderedInterval (36799423398 / 1000000000000) (36799423399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1163172772271853 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26030071128 / 1000000000000) (26030075709 / 1000000000000), orderedInterval (-38925206255 / 1000000000000) (-38925201674 / 1000000000000)))) (orderedInterval (-10951839035 / 1000000000000) (-10951837723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (856787799477589 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53234657862 / 1000000000000) (53234657865 / 1000000000000), orderedInterval (11631043732 / 1000000000000) (11631043735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1468120497885097 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10257006205 / 1000000000000) (-10257006204 / 1000000000000), orderedInterval (-40350759725 / 1000000000000) (-40350759724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1081410913955323 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39771436286 / 1000000000000) (39771436287 / 1000000000000), orderedInterval (27729434572 / 1000000000000) (27729434573 / 1000000000000)))) (orderedInterval (-11697173969 / 1000000000000) (-11697173910 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate312_chunkChecks3_1 :
    compactCertificate312.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1659162439304629 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30331082427 / 1000000000000) (30331082428 / 1000000000000), orderedInterval (24759065859 / 1000000000000) (24759065860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (957917880961741 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51441729599 / 1000000000000) (51441729633 / 1000000000000), orderedInterval (3369768440 / 1000000000000) (3369768474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1699842089619569 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38635635689 / 1000000000000) (-38635634999 / 1000000000000), orderedInterval (2359475787 / 1000000000000) (2359476477 / 1000000000000)))) (orderedInterval (44349825360 / 1000000000000) (44349827266 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1588212977839061 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36449053092 / 1000000000000) (36449081905 / 1000000000000), orderedInterval (-16623785002 / 1000000000000) (-16623756189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1133423721885413 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46689914922 / 1000000000000) (46689914932 / 1000000000000), orderedInterval (8088456307 / 1000000000000) (8088456316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1285181699215827 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44412637685 / 1000000000000) (44412638078 / 1000000000000), orderedInterval (-3057565279 / 1000000000000) (-3057564886 / 1000000000000)))) (orderedInterval (-5713842669 / 1000000000000) (-5713837440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1071450513878563 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48709261713 / 1000000000000) (-48709261516 / 1000000000000), orderedInterval (2108060751 / 1000000000000) (2108060948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (946659022845823 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50129885100 / 1000000000000) (-50129882767 / 1000000000000), orderedInterval (13408310895 / 1000000000000) (13408313229 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (274378682628477 / 800000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41786221816 / 1000000000000) (-41786221811 / 1000000000000), orderedInterval (-10431386920 / 1000000000000) (-10431386915 / 1000000000000)))) (orderedInterval (3207316380 / 1000000000000) (3207316725 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate312_chunkChecks3_2 :
    compactCertificate312.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (758945875909319 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52035252722 / 1000000000000) (52035266661 / 1000000000000), orderedInterval (-25585288810 / 1000000000000) (-25585274870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (643366824103759 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-62051242524 / 1000000000000) (-62051242520 / 1000000000000), orderedInterval (-10183850756 / 1000000000000) (-10183850752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (402589086044677 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62321639274 / 1000000000000) (62321639275 / 1000000000000), orderedInterval (49099427093 / 1000000000000) (49099427094 / 1000000000000)))) (orderedInterval (-5037833249 / 1000000000000) (-5037830810 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (216513749425659 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-108208543723 / 1000000000000) (-108208543714 / 1000000000000), orderedInterval (-6190467477 / 1000000000000) (-6190467469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (587876947613977 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6500463021 / 1000000000000) (-6500463020 / 1000000000000), orderedInterval (-65471562806 / 1000000000000) (-65471562804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (802695712820729 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21766129692 / 1000000000000) (21766129693 / 1000000000000), orderedInterval (51894314285 / 1000000000000) (51894314286 / 1000000000000)))) (orderedInterval (4284283034 / 1000000000000) (4284283055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (339410913955323 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62953303470 / 1000000000000) (-62953303469 / 1000000000000), orderedInterval (-59122902796 / 1000000000000) (-59122902795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1379686521697883 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5632076905 / 1000000000000) (5632076906 / 1000000000000), orderedInterval (42582627569 / 1000000000000) (42582627570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (921566656214197 / 4000000000000) 3 (IntervalRat.scale (371 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50669295810 / 1000000000000) (-50669293290 / 1000000000000), orderedInterval (14103661034 / 1000000000000) (14103663554 / 1000000000000)))) (orderedInterval (27457606922 / 1000000000000) (27457607997 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate312_chunkChecks3 :
    compactCertificate312.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate312.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate312_chunkChecks3_0
    compactCertificate312_chunkChecks3_1 compactCertificate312_chunkChecks3_2

theorem compactCertificate312_chunkChecks4_0 :
    compactCertificate312.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (371 / 2) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46987361999 / 1000000000000) (-46987361998 / 1000000000000), orderedInterval (-34860444521 / 1000000000000) (-34860444520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (546553841671271 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49303130984 / 1000000000000) (-49303055745 / 1000000000000), orderedInterval (47385864852 / 1000000000000) (47385940090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (176744282739143 / 800000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52230572018 / 1000000000000) (52230573599 / 1000000000000), orderedInterval (-12507767016 / 1000000000000) (-12507765436 / 1000000000000)))) (orderedInterval (-12751617818 / 1000000000000) (-12751617397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (159483047874997 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23575322665 / 1000000000000) (23575322829 / 1000000000000), orderedInterval (-124442506551 / 1000000000000) (-124442506387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (428393899738609 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67577331239 / 1000000000000) (67577331240 / 1000000000000), orderedInterval (36799423398 / 1000000000000) (36799423399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1163172772271853 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26030071128 / 1000000000000) (26030075709 / 1000000000000), orderedInterval (-38925206255 / 1000000000000) (-38925201674 / 1000000000000)))) (orderedInterval (-10783092557 / 1000000000000) (-10783090495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (856787799477589 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53234657862 / 1000000000000) (53234657865 / 1000000000000), orderedInterval (11631043732 / 1000000000000) (11631043735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1468120497885097 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10257006205 / 1000000000000) (-10257006204 / 1000000000000), orderedInterval (-40350759725 / 1000000000000) (-40350759724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1081410913955323 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39771436286 / 1000000000000) (39771436287 / 1000000000000), orderedInterval (27729434572 / 1000000000000) (27729434573 / 1000000000000)))) (orderedInterval (9311392013 / 1000000000000) (9311392122 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate312_chunkChecks4_1 :
    compactCertificate312.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1659162439304629 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30331082427 / 1000000000000) (30331082428 / 1000000000000), orderedInterval (24759065859 / 1000000000000) (24759065860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (957917880961741 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51441729599 / 1000000000000) (51441729633 / 1000000000000), orderedInterval (3369768440 / 1000000000000) (3369768474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1699842089619569 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38635635689 / 1000000000000) (-38635634999 / 1000000000000), orderedInterval (2359475787 / 1000000000000) (2359476477 / 1000000000000)))) (orderedInterval (-275902711605 / 1000000000000) (-275902707289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1588212977839061 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36449053092 / 1000000000000) (36449081905 / 1000000000000), orderedInterval (-16623785002 / 1000000000000) (-16623756189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1133423721885413 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46689914922 / 1000000000000) (46689914932 / 1000000000000), orderedInterval (8088456307 / 1000000000000) (8088456316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1285181699215827 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44412637685 / 1000000000000) (44412638078 / 1000000000000), orderedInterval (-3057565279 / 1000000000000) (-3057564886 / 1000000000000)))) (orderedInterval (8264545963 / 1000000000000) (8264557135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1071450513878563 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48709261713 / 1000000000000) (-48709261516 / 1000000000000), orderedInterval (2108060751 / 1000000000000) (2108060948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (946659022845823 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-50129885100 / 1000000000000) (-50129882767 / 1000000000000), orderedInterval (13408310895 / 1000000000000) (13408313229 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (274378682628477 / 800000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41786221816 / 1000000000000) (-41786221811 / 1000000000000), orderedInterval (-10431386920 / 1000000000000) (-10431386915 / 1000000000000)))) (orderedInterval (-7382193294 / 1000000000000) (-7382192832 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate312_chunkChecks4_2 :
    compactCertificate312.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (758945875909319 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (52035252722 / 1000000000000) (52035266661 / 1000000000000), orderedInterval (-25585288810 / 1000000000000) (-25585274870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (643366824103759 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-62051242524 / 1000000000000) (-62051242520 / 1000000000000), orderedInterval (-10183850756 / 1000000000000) (-10183850752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (402589086044677 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62321639274 / 1000000000000) (62321639275 / 1000000000000), orderedInterval (49099427093 / 1000000000000) (49099427094 / 1000000000000)))) (orderedInterval (-6891120473 / 1000000000000) (-6891117968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (216513749425659 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-108208543723 / 1000000000000) (-108208543714 / 1000000000000), orderedInterval (-6190467477 / 1000000000000) (-6190467469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (587876947613977 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6500463021 / 1000000000000) (-6500463020 / 1000000000000), orderedInterval (-65471562806 / 1000000000000) (-65471562804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (802695712820729 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21766129692 / 1000000000000) (21766129693 / 1000000000000), orderedInterval (51894314285 / 1000000000000) (51894314286 / 1000000000000)))) (orderedInterval (-2258189820 / 1000000000000) (-2258189798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (339410913955323 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62953303470 / 1000000000000) (-62953303469 / 1000000000000), orderedInterval (-59122902796 / 1000000000000) (-59122902795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1379686521697883 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5632076905 / 1000000000000) (5632076906 / 1000000000000), orderedInterval (42582627569 / 1000000000000) (42582627570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (921566656214197 / 4000000000000) 4 (IntervalRat.scale (371 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50669295810 / 1000000000000) (-50669293290 / 1000000000000), orderedInterval (14103661034 / 1000000000000) (14103663554 / 1000000000000)))) (orderedInterval (16828591095 / 1000000000000) (16828592495 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate312_chunkChecks4 :
    compactCertificate312.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate312.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate312_chunkChecks4_0
    compactCertificate312_chunkChecks4_1 compactCertificate312_chunkChecks4_2

theorem compactCertificate312_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate312.chunkCheck r b = true :=
  compactCertificate312.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate312_chunkChecks0
    · exact compactCertificate312_chunkChecks1
    · exact compactCertificate312_chunkChecks2
    · exact compactCertificate312_chunkChecks3
    · exact compactCertificate312_chunkChecks4)

theorem compactCertificate312_coefficient0 :
    compactCertificate312.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate312_coefficient1 :
    compactCertificate312.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate312_coefficient2 :
    compactCertificate312.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate312_coefficient3 :
    compactCertificate312.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate312_coefficient4 :
    compactCertificate312.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate312_coefficients : ∀ r : Fin 5,
    compactCertificate312.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate312_coefficient0
  · exact compactCertificate312_coefficient1
  · exact compactCertificate312_coefficient2
  · exact compactCertificate312_coefficient3
  · exact compactCertificate312_coefficient4

theorem compactCertificate312_lower : (1 : ℚ) ≤ compactCertificate312.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate312, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate312_proves {t : ℝ} (ht : t ∈ compactCertificate312.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate312.proves compactCertificate312_states compactCertificate312_chunks
    compactCertificate312_coefficients compactCertificate312_lower ht

end Erdos232
