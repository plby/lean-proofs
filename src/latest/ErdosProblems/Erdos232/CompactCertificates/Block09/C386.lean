/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate386 : CompactCertificate where
  left := 257
  right := 258
  center := 515 / 2
  grid := fun i =>
    match i.val with
    | 0 => 82
    | 1 => 60
    | 2 => 98
    | 3 => 18
    | 4 => 47
    | 5 => 129
    | 6 => 95
    | 7 => 162
    | 8 => 120
    | 9 => 183
    | 10 => 106
    | 11 => 188
    | 12 => 176
    | 13 => 125
    | 14 => 142
    | 15 => 118
    | 16 => 105
    | 17 => 152
    | 18 => 84
    | 19 => 71
    | 20 => 44
    | 21 => 24
    | 22 => 65
    | 23 => 89
    | 24 => 38
    | 25 => 152
    | _ => 102
  point := fun i =>
    match i.val with
    | 0 => 515 / 2
    | 1 => 151738667633803 / 800000000000
    | 2 => 49069167445099 / 160000000000
    | 3 => 44276964773921 / 800000000000
    | 4 => 118934155453037 / 800000000000
    | 5 => 322929368043129 / 800000000000
    | 6 => 237868310906177 / 800000000000
    | 7 => 407591405073221 / 800000000000
    | 8 => 300229984197839 / 800000000000
    | 9 => 460630003364897 / 800000000000
    | 10 => 265944856439513 / 800000000000
    | 11 => 471923814638317 / 800000000000
    | 12 => 440932443982273 / 800000000000
    | 13 => 314670197720209 / 800000000000
    | 14 => 356802466359111 / 800000000000
    | 15 => 297464697923159 / 800000000000
    | 16 => 262819081814339 / 800000000000
    | 17 => 76175213775561 / 160000000000
    | 18 => 210704650185067 / 800000000000
    | 19 => 178616665451987 / 800000000000
    | 20 => 111770015802161 / 800000000000
    | 21 => 60110286228687 / 800000000000
    | 22 => 163211120227061 / 800000000000
    | 23 => 222850831322197 / 800000000000
    | 24 => 94229984197839 / 800000000000
    | 25 => 383039654271919 / 800000000000
    | _ => 255852737439521 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (31044726694 / 1000000000000) (31044726695 / 1000000000000), orderedInterval (38779592620 / 1000000000000) (38779592621 / 1000000000000))
    | 1 => (orderedInterval (53546081974 / 1000000000000) (53546089406 / 1000000000000), orderedInterval (-22259235573 / 1000000000000) (-22259228142 / 1000000000000))
    | 2 => (orderedInterval (-18110680354 / 1000000000000) (-18110679834 / 1000000000000), orderedInterval (41836623854 / 1000000000000) (41836624375 / 1000000000000))
    | 3 => (orderedInterval (-43664872829 / 1000000000000) (-43664870249 / 1000000000000), orderedInterval (98354598519 / 1000000000000) (98354601099 / 1000000000000))
    | 4 => (orderedInterval (-63765201920 / 1000000000000) (-63765200961 / 1000000000000), orderedInterval (14916271786 / 1000000000000) (14916272745 / 1000000000000))
    | 5 => (orderedInterval (28999375888 / 1000000000000) (28999400980 / 1000000000000), orderedInterval (-27167970508 / 1000000000000) (-27167945416 / 1000000000000))
    | 6 => (orderedInterval (15035009629 / 1000000000000) (15035009831 / 1000000000000), orderedInterval (-43786383924 / 1000000000000) (-43786383722 / 1000000000000))
    | 7 => (orderedInterval (34381994607 / 1000000000000) (34381994629 / 1000000000000), orderedInterval (8176210899 / 1000000000000) (8176210921 / 1000000000000))
    | 8 => (orderedInterval (-32732664635 / 1000000000000) (-32732594993 / 1000000000000), orderedInterval (25042109375 / 1000000000000) (25042179017 / 1000000000000))
    | 9 => (orderedInterval (-33115443830 / 1000000000000) (-33115441424 / 1000000000000), orderedInterval (3031687340 / 1000000000000) (3031689746 / 1000000000000))
    | 10 => (orderedInterval (9005634328 / 1000000000000) (9005634329 / 1000000000000), orderedInterval (42811021066 / 1000000000000) (42811021067 / 1000000000000))
    | 11 => (orderedInterval (2315249264 / 1000000000000) (2315249265 / 1000000000000), orderedInterval (32767394633 / 1000000000000) (32767394634 / 1000000000000))
    | 12 => (orderedInterval (-28026459599 / 1000000000000) (-28026409603 / 1000000000000), orderedInterval (19249381452 / 1000000000000) (19249431448 / 1000000000000))
    | 13 => (orderedInterval (-39796464640 / 1000000000000) (-39796464607 / 1000000000000), orderedInterval (-5844056524 / 1000000000000) (-5844056491 / 1000000000000))
    | 14 => (orderedInterval (23816293608 / 1000000000000) (23816293609 / 1000000000000), orderedInterval (29302007585 / 1000000000000) (29302007586 / 1000000000000))
    | 15 => (orderedInterval (39047502043 / 1000000000000) (39047512884 / 1000000000000), orderedInterval (-13742392419 / 1000000000000) (-13742381578 / 1000000000000))
    | 16 => (orderedInterval (23321908078 / 1000000000000) (23321910726 / 1000000000000), orderedInterval (-37370580957 / 1000000000000) (-37370578309 / 1000000000000))
    | 17 => (orderedInterval (-21892401054 / 1000000000000) (-21892398138 / 1000000000000), orderedInterval (29312790891 / 1000000000000) (29312793807 / 1000000000000))
    | 18 => (orderedInterval (13206128806 / 1000000000000) (13206128807 / 1000000000000), orderedInterval (47332183826 / 1000000000000) (47332183827 / 1000000000000))
    | 19 => (orderedInterval (-45007338307 / 1000000000000) (-45007338306 / 1000000000000), orderedInterval (-28633696741 / 1000000000000) (-28633696740 / 1000000000000))
    | 20 => (orderedInterval (51795878255 / 1000000000000) (51795976032 / 1000000000000), orderedInterval (-43473022219 / 1000000000000) (-43472924442 / 1000000000000))
    | 21 => (orderedInterval (46004765624 / 1000000000000) (46004765625 / 1000000000000), orderedInterval (79420569293 / 1000000000000) (79420569294 / 1000000000000))
    | 22 => (orderedInterval (-31318191526 / 1000000000000) (-31318191525 / 1000000000000), orderedInterval (-46179562755 / 1000000000000) (-46179562754 / 1000000000000))
    | 23 => (orderedInterval (11978087954 / 1000000000000) (11978088032 / 1000000000000), orderedInterval (-46302112259 / 1000000000000) (-46302112181 / 1000000000000))
    | 24 => (orderedInterval (-53181794518 / 1000000000000) (-53181711907 / 1000000000000), orderedInterval (50985094842 / 1000000000000) (50985177452 / 1000000000000))
    | 25 => (orderedInterval (32141878847 / 1000000000000) (32141952828 / 1000000000000), orderedInterval (-17253160089 / 1000000000000) (-17253086109 / 1000000000000))
    | _ => (orderedInterval (7041100258 / 1000000000000) (7041100259 / 1000000000000), orderedInterval (44045853850 / 1000000000000) (44045853851 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11741233105 / 1000000000000) (11741233223 / 1000000000000)
      | 1 => orderedInterval (-3916002993 / 1000000000000) (-3916001115 / 1000000000000)
      | 2 => orderedInterval (-1851562207 / 1000000000000) (-1851560508 / 1000000000000)
      | 3 => orderedInterval (6880583775 / 1000000000000) (6880584305 / 1000000000000)
      | 4 => orderedInterval (-3377828750 / 1000000000000) (-3377827813 / 1000000000000)
      | 5 => orderedInterval (-1444259739 / 1000000000000) (-1444259362 / 1000000000000)
      | 6 => orderedInterval (2122082004 / 1000000000000) (2122085253 / 1000000000000)
      | 7 => orderedInterval (-1056959038 / 1000000000000) (-1056959000 / 1000000000000)
      | _ => orderedInterval (-4258106601 / 1000000000000) (-4258100009 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18142021360 / 1000000000000) (18142021469 / 1000000000000)
      | 1 => orderedInterval (3112716259 / 1000000000000) (3112719117 / 1000000000000)
      | 2 => orderedInterval (383084580 / 1000000000000) (383087060 / 1000000000000)
      | 3 => orderedInterval (13561560109 / 1000000000000) (13561561277 / 1000000000000)
      | 4 => orderedInterval (-1844825493 / 1000000000000) (-1844823506 / 1000000000000)
      | 5 => orderedInterval (3886962134 / 1000000000000) (3886962683 / 1000000000000)
      | 6 => orderedInterval (-7103556246 / 1000000000000) (-7103554459 / 1000000000000)
      | 7 => orderedInterval (4240943601 / 1000000000000) (4240943636 / 1000000000000)
      | _ => orderedInterval (-7512114250 / 1000000000000) (-7512102724 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11138715485 / 1000000000000) (-11138715380 / 1000000000000)
      | 1 => orderedInterval (5808207622 / 1000000000000) (5808212078 / 1000000000000)
      | 2 => orderedInterval (5830462970 / 1000000000000) (5830466603 / 1000000000000)
      | 3 => orderedInterval (-32313128153 / 1000000000000) (-32313125557 / 1000000000000)
      | 4 => orderedInterval (6831609873 / 1000000000000) (6831614106 / 1000000000000)
      | 5 => orderedInterval (3133273777 / 1000000000000) (3133274596 / 1000000000000)
      | 6 => orderedInterval (-174882887 / 1000000000000) (-174881885 / 1000000000000)
      | 7 => orderedInterval (684171492 / 1000000000000) (684171528 / 1000000000000)
      | _ => orderedInterval (11180176601 / 1000000000000) (11180197719 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19391978876 / 1000000000000) (-19391978769 / 1000000000000)
      | 1 => orderedInterval (-7556923466 / 1000000000000) (-7556916497 / 1000000000000)
      | 2 => orderedInterval (57198739 / 1000000000000) (57204050 / 1000000000000)
      | 3 => orderedInterval (-56680686651 / 1000000000000) (-56680680867 / 1000000000000)
      | 4 => orderedInterval (6121521554 / 1000000000000) (6121530573 / 1000000000000)
      | 5 => orderedInterval (-8719123425 / 1000000000000) (-8719122176 / 1000000000000)
      | 6 => orderedInterval (7268666699 / 1000000000000) (7268667267 / 1000000000000)
      | 7 => orderedInterval (-4979728272 / 1000000000000) (-4979728235 / 1000000000000)
      | _ => orderedInterval (6731375955 / 1000000000000) (6731415027 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10464021375 / 1000000000000) (10464021490 / 1000000000000)
      | 1 => orderedInterval (-12648529157 / 1000000000000) (-12648518215 / 1000000000000)
      | 2 => orderedInterval (-19822527279 / 1000000000000) (-19822519483 / 1000000000000)
      | 3 => orderedInterval (158463837461 / 1000000000000) (158463850396 / 1000000000000)
      | 4 => orderedInterval (-11000726542 / 1000000000000) (-11000707268 / 1000000000000)
      | 5 => orderedInterval (-8058210513 / 1000000000000) (-8058208555 / 1000000000000)
      | 6 => orderedInterval (-781636339 / 1000000000000) (-781636004 / 1000000000000)
      | 7 => orderedInterval (-944766646 / 1000000000000) (-944766607 / 1000000000000)
      | _ => orderedInterval (-34485814426 / 1000000000000) (-34485741749 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4839179556 / 1000000000000) (4839194974 / 1000000000000)
    | 1 => orderedInterval (26866792054 / 1000000000000) (26866814553 / 1000000000000)
    | 2 => orderedInterval (-10158824190 / 1000000000000) (-10158786192 / 1000000000000)
    | 3 => orderedInterval (-77149677743 / 1000000000000) (-77149609627 / 1000000000000)
    | _ => orderedInterval (81185647934 / 1000000000000) (81185774005 / 1000000000000)

theorem compactCertificate386_stateChecks0 :
    compactCertificate386.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (515 / 2)) (orderedInterval (31044726694 / 1000000000000) (31044726695 / 1000000000000), orderedInterval (38779592620 / 1000000000000) (38779592621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (151738667633803 / 800000000000)) (orderedInterval (53546081974 / 1000000000000) (53546089406 / 1000000000000), orderedInterval (-22259235573 / 1000000000000) (-22259228142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (49069167445099 / 160000000000)) (orderedInterval (-18110680354 / 1000000000000) (-18110679834 / 1000000000000), orderedInterval (41836623854 / 1000000000000) (41836624375 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_stateChecks1 :
    compactCertificate386.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (44276964773921 / 800000000000)) (orderedInterval (-43664872829 / 1000000000000) (-43664870249 / 1000000000000), orderedInterval (98354598519 / 1000000000000) (98354601099 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (118934155453037 / 800000000000)) (orderedInterval (-63765201920 / 1000000000000) (-63765200961 / 1000000000000), orderedInterval (14916271786 / 1000000000000) (14916272745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (322929368043129 / 800000000000)) (orderedInterval (28999375888 / 1000000000000) (28999400980 / 1000000000000), orderedInterval (-27167970508 / 1000000000000) (-27167945416 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_stateChecks2 :
    compactCertificate386.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (237868310906177 / 800000000000)) (orderedInterval (15035009629 / 1000000000000) (15035009831 / 1000000000000), orderedInterval (-43786383924 / 1000000000000) (-43786383722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (407591405073221 / 800000000000)) (orderedInterval (34381994607 / 1000000000000) (34381994629 / 1000000000000), orderedInterval (8176210899 / 1000000000000) (8176210921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (300229984197839 / 800000000000)) (orderedInterval (-32732664635 / 1000000000000) (-32732594993 / 1000000000000), orderedInterval (25042109375 / 1000000000000) (25042179017 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_stateChecks3 :
    compactCertificate386.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (460630003364897 / 800000000000)) (orderedInterval (-33115443830 / 1000000000000) (-33115441424 / 1000000000000), orderedInterval (3031687340 / 1000000000000) (3031689746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (265944856439513 / 800000000000)) (orderedInterval (9005634328 / 1000000000000) (9005634329 / 1000000000000), orderedInterval (42811021066 / 1000000000000) (42811021067 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (471923814638317 / 800000000000)) (orderedInterval (2315249264 / 1000000000000) (2315249265 / 1000000000000), orderedInterval (32767394633 / 1000000000000) (32767394634 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_stateChecks4 :
    compactCertificate386.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (440932443982273 / 800000000000)) (orderedInterval (-28026459599 / 1000000000000) (-28026409603 / 1000000000000), orderedInterval (19249381452 / 1000000000000) (19249431448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (314670197720209 / 800000000000)) (orderedInterval (-39796464640 / 1000000000000) (-39796464607 / 1000000000000), orderedInterval (-5844056524 / 1000000000000) (-5844056491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (356802466359111 / 800000000000)) (orderedInterval (23816293608 / 1000000000000) (23816293609 / 1000000000000), orderedInterval (29302007585 / 1000000000000) (29302007586 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_stateChecks5 :
    compactCertificate386.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (297464697923159 / 800000000000)) (orderedInterval (39047502043 / 1000000000000) (39047512884 / 1000000000000), orderedInterval (-13742392419 / 1000000000000) (-13742381578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (262819081814339 / 800000000000)) (orderedInterval (23321908078 / 1000000000000) (23321910726 / 1000000000000), orderedInterval (-37370580957 / 1000000000000) (-37370578309 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (76175213775561 / 160000000000)) (orderedInterval (-21892401054 / 1000000000000) (-21892398138 / 1000000000000), orderedInterval (29312790891 / 1000000000000) (29312793807 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_stateChecks6 :
    compactCertificate386.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (210704650185067 / 800000000000)) (orderedInterval (13206128806 / 1000000000000) (13206128807 / 1000000000000), orderedInterval (47332183826 / 1000000000000) (47332183827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (178616665451987 / 800000000000)) (orderedInterval (-45007338307 / 1000000000000) (-45007338306 / 1000000000000), orderedInterval (-28633696741 / 1000000000000) (-28633696740 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (111770015802161 / 800000000000)) (orderedInterval (51795878255 / 1000000000000) (51795976032 / 1000000000000), orderedInterval (-43473022219 / 1000000000000) (-43472924442 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_stateChecks7 :
    compactCertificate386.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (60110286228687 / 800000000000)) (orderedInterval (46004765624 / 1000000000000) (46004765625 / 1000000000000), orderedInterval (79420569293 / 1000000000000) (79420569294 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (163211120227061 / 800000000000)) (orderedInterval (-31318191526 / 1000000000000) (-31318191525 / 1000000000000), orderedInterval (-46179562755 / 1000000000000) (-46179562754 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (222850831322197 / 800000000000)) (orderedInterval (11978087954 / 1000000000000) (11978088032 / 1000000000000), orderedInterval (-46302112259 / 1000000000000) (-46302112181 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_stateChecks8 :
    compactCertificate386.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (94229984197839 / 800000000000)) (orderedInterval (-53181794518 / 1000000000000) (-53181711907 / 1000000000000), orderedInterval (50985094842 / 1000000000000) (50985177452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (383039654271919 / 800000000000)) (orderedInterval (32141878847 / 1000000000000) (32141952828 / 1000000000000), orderedInterval (-17253160089 / 1000000000000) (-17253086109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (255852737439521 / 800000000000)) (orderedInterval (7041100258 / 1000000000000) (7041100259 / 1000000000000), orderedInterval (44045853850 / 1000000000000) (44045853851 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_states : ∀ j,
    BesselStateValid (compactCertificate386.point j) (compactCertificate386.state j) :=
  compactCertificate386.statesValid_of_checks3 compactCertificate386_stateChecks0
    compactCertificate386_stateChecks1 compactCertificate386_stateChecks2
    compactCertificate386_stateChecks3 compactCertificate386_stateChecks4
    compactCertificate386_stateChecks5 compactCertificate386_stateChecks6
    compactCertificate386_stateChecks7 compactCertificate386_stateChecks8

theorem compactCertificate386_chunkChecks0_0 :
    compactCertificate386.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (515 / 2) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31044726694 / 1000000000000) (31044726695 / 1000000000000), orderedInterval (38779592620 / 1000000000000) (38779592621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (151738667633803 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53546081974 / 1000000000000) (53546089406 / 1000000000000), orderedInterval (-22259235573 / 1000000000000) (-22259228142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (49069167445099 / 160000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18110680354 / 1000000000000) (-18110679834 / 1000000000000), orderedInterval (41836623854 / 1000000000000) (41836624375 / 1000000000000)))) (orderedInterval (11741233105 / 1000000000000) (11741233223 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (44276964773921 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-43664872829 / 1000000000000) (-43664870249 / 1000000000000), orderedInterval (98354598519 / 1000000000000) (98354601099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (118934155453037 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63765201920 / 1000000000000) (-63765200961 / 1000000000000), orderedInterval (14916271786 / 1000000000000) (14916272745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (322929368043129 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28999375888 / 1000000000000) (28999400980 / 1000000000000), orderedInterval (-27167970508 / 1000000000000) (-27167945416 / 1000000000000)))) (orderedInterval (-3916002993 / 1000000000000) (-3916001115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (237868310906177 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15035009629 / 1000000000000) (15035009831 / 1000000000000), orderedInterval (-43786383924 / 1000000000000) (-43786383722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (407591405073221 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34381994607 / 1000000000000) (34381994629 / 1000000000000), orderedInterval (8176210899 / 1000000000000) (8176210921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (300229984197839 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32732664635 / 1000000000000) (-32732594993 / 1000000000000), orderedInterval (25042109375 / 1000000000000) (25042179017 / 1000000000000)))) (orderedInterval (-1851562207 / 1000000000000) (-1851560508 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks0_1 :
    compactCertificate386.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (460630003364897 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33115443830 / 1000000000000) (-33115441424 / 1000000000000), orderedInterval (3031687340 / 1000000000000) (3031689746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (265944856439513 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9005634328 / 1000000000000) (9005634329 / 1000000000000), orderedInterval (42811021066 / 1000000000000) (42811021067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (471923814638317 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2315249264 / 1000000000000) (2315249265 / 1000000000000), orderedInterval (32767394633 / 1000000000000) (32767394634 / 1000000000000)))) (orderedInterval (6880583775 / 1000000000000) (6880584305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (440932443982273 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28026459599 / 1000000000000) (-28026409603 / 1000000000000), orderedInterval (19249381452 / 1000000000000) (19249431448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (314670197720209 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39796464640 / 1000000000000) (-39796464607 / 1000000000000), orderedInterval (-5844056524 / 1000000000000) (-5844056491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (356802466359111 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23816293608 / 1000000000000) (23816293609 / 1000000000000), orderedInterval (29302007585 / 1000000000000) (29302007586 / 1000000000000)))) (orderedInterval (-3377828750 / 1000000000000) (-3377827813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (297464697923159 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39047502043 / 1000000000000) (39047512884 / 1000000000000), orderedInterval (-13742392419 / 1000000000000) (-13742381578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (262819081814339 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23321908078 / 1000000000000) (23321910726 / 1000000000000), orderedInterval (-37370580957 / 1000000000000) (-37370578309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (76175213775561 / 160000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21892401054 / 1000000000000) (-21892398138 / 1000000000000), orderedInterval (29312790891 / 1000000000000) (29312793807 / 1000000000000)))) (orderedInterval (-1444259739 / 1000000000000) (-1444259362 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks0_2 :
    compactCertificate386.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (210704650185067 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13206128806 / 1000000000000) (13206128807 / 1000000000000), orderedInterval (47332183826 / 1000000000000) (47332183827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (178616665451987 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45007338307 / 1000000000000) (-45007338306 / 1000000000000), orderedInterval (-28633696741 / 1000000000000) (-28633696740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (111770015802161 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51795878255 / 1000000000000) (51795976032 / 1000000000000), orderedInterval (-43473022219 / 1000000000000) (-43472924442 / 1000000000000)))) (orderedInterval (2122082004 / 1000000000000) (2122085253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (60110286228687 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (46004765624 / 1000000000000) (46004765625 / 1000000000000), orderedInterval (79420569293 / 1000000000000) (79420569294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (163211120227061 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31318191526 / 1000000000000) (-31318191525 / 1000000000000), orderedInterval (-46179562755 / 1000000000000) (-46179562754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (222850831322197 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11978087954 / 1000000000000) (11978088032 / 1000000000000), orderedInterval (-46302112259 / 1000000000000) (-46302112181 / 1000000000000)))) (orderedInterval (-1056959038 / 1000000000000) (-1056959000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (94229984197839 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53181794518 / 1000000000000) (-53181711907 / 1000000000000), orderedInterval (50985094842 / 1000000000000) (50985177452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (383039654271919 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32141878847 / 1000000000000) (32141952828 / 1000000000000), orderedInterval (-17253160089 / 1000000000000) (-17253086109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (255852737439521 / 800000000000) 0 (IntervalRat.scale (515 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7041100258 / 1000000000000) (7041100259 / 1000000000000), orderedInterval (44045853850 / 1000000000000) (44045853851 / 1000000000000)))) (orderedInterval (-4258106601 / 1000000000000) (-4258100009 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks0 :
    compactCertificate386.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate386.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate386_chunkChecks0_0
    compactCertificate386_chunkChecks0_1 compactCertificate386_chunkChecks0_2

theorem compactCertificate386_chunkChecks1_0 :
    compactCertificate386.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (515 / 2) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31044726694 / 1000000000000) (31044726695 / 1000000000000), orderedInterval (38779592620 / 1000000000000) (38779592621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (151738667633803 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53546081974 / 1000000000000) (53546089406 / 1000000000000), orderedInterval (-22259235573 / 1000000000000) (-22259228142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (49069167445099 / 160000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18110680354 / 1000000000000) (-18110679834 / 1000000000000), orderedInterval (41836623854 / 1000000000000) (41836624375 / 1000000000000)))) (orderedInterval (18142021360 / 1000000000000) (18142021469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (44276964773921 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-43664872829 / 1000000000000) (-43664870249 / 1000000000000), orderedInterval (98354598519 / 1000000000000) (98354601099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (118934155453037 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63765201920 / 1000000000000) (-63765200961 / 1000000000000), orderedInterval (14916271786 / 1000000000000) (14916272745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (322929368043129 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28999375888 / 1000000000000) (28999400980 / 1000000000000), orderedInterval (-27167970508 / 1000000000000) (-27167945416 / 1000000000000)))) (orderedInterval (3112716259 / 1000000000000) (3112719117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (237868310906177 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15035009629 / 1000000000000) (15035009831 / 1000000000000), orderedInterval (-43786383924 / 1000000000000) (-43786383722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (407591405073221 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34381994607 / 1000000000000) (34381994629 / 1000000000000), orderedInterval (8176210899 / 1000000000000) (8176210921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (300229984197839 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32732664635 / 1000000000000) (-32732594993 / 1000000000000), orderedInterval (25042109375 / 1000000000000) (25042179017 / 1000000000000)))) (orderedInterval (383084580 / 1000000000000) (383087060 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks1_1 :
    compactCertificate386.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (460630003364897 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33115443830 / 1000000000000) (-33115441424 / 1000000000000), orderedInterval (3031687340 / 1000000000000) (3031689746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (265944856439513 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9005634328 / 1000000000000) (9005634329 / 1000000000000), orderedInterval (42811021066 / 1000000000000) (42811021067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (471923814638317 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2315249264 / 1000000000000) (2315249265 / 1000000000000), orderedInterval (32767394633 / 1000000000000) (32767394634 / 1000000000000)))) (orderedInterval (13561560109 / 1000000000000) (13561561277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (440932443982273 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28026459599 / 1000000000000) (-28026409603 / 1000000000000), orderedInterval (19249381452 / 1000000000000) (19249431448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (314670197720209 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39796464640 / 1000000000000) (-39796464607 / 1000000000000), orderedInterval (-5844056524 / 1000000000000) (-5844056491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (356802466359111 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23816293608 / 1000000000000) (23816293609 / 1000000000000), orderedInterval (29302007585 / 1000000000000) (29302007586 / 1000000000000)))) (orderedInterval (-1844825493 / 1000000000000) (-1844823506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (297464697923159 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39047502043 / 1000000000000) (39047512884 / 1000000000000), orderedInterval (-13742392419 / 1000000000000) (-13742381578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (262819081814339 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23321908078 / 1000000000000) (23321910726 / 1000000000000), orderedInterval (-37370580957 / 1000000000000) (-37370578309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (76175213775561 / 160000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21892401054 / 1000000000000) (-21892398138 / 1000000000000), orderedInterval (29312790891 / 1000000000000) (29312793807 / 1000000000000)))) (orderedInterval (3886962134 / 1000000000000) (3886962683 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks1_2 :
    compactCertificate386.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (210704650185067 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13206128806 / 1000000000000) (13206128807 / 1000000000000), orderedInterval (47332183826 / 1000000000000) (47332183827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (178616665451987 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45007338307 / 1000000000000) (-45007338306 / 1000000000000), orderedInterval (-28633696741 / 1000000000000) (-28633696740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (111770015802161 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51795878255 / 1000000000000) (51795976032 / 1000000000000), orderedInterval (-43473022219 / 1000000000000) (-43472924442 / 1000000000000)))) (orderedInterval (-7103556246 / 1000000000000) (-7103554459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (60110286228687 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (46004765624 / 1000000000000) (46004765625 / 1000000000000), orderedInterval (79420569293 / 1000000000000) (79420569294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (163211120227061 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31318191526 / 1000000000000) (-31318191525 / 1000000000000), orderedInterval (-46179562755 / 1000000000000) (-46179562754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (222850831322197 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11978087954 / 1000000000000) (11978088032 / 1000000000000), orderedInterval (-46302112259 / 1000000000000) (-46302112181 / 1000000000000)))) (orderedInterval (4240943601 / 1000000000000) (4240943636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (94229984197839 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53181794518 / 1000000000000) (-53181711907 / 1000000000000), orderedInterval (50985094842 / 1000000000000) (50985177452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (383039654271919 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32141878847 / 1000000000000) (32141952828 / 1000000000000), orderedInterval (-17253160089 / 1000000000000) (-17253086109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (255852737439521 / 800000000000) 1 (IntervalRat.scale (515 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7041100258 / 1000000000000) (7041100259 / 1000000000000), orderedInterval (44045853850 / 1000000000000) (44045853851 / 1000000000000)))) (orderedInterval (-7512114250 / 1000000000000) (-7512102724 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks1 :
    compactCertificate386.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate386.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate386_chunkChecks1_0
    compactCertificate386_chunkChecks1_1 compactCertificate386_chunkChecks1_2

theorem compactCertificate386_chunkChecks2_0 :
    compactCertificate386.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (515 / 2) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31044726694 / 1000000000000) (31044726695 / 1000000000000), orderedInterval (38779592620 / 1000000000000) (38779592621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (151738667633803 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53546081974 / 1000000000000) (53546089406 / 1000000000000), orderedInterval (-22259235573 / 1000000000000) (-22259228142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (49069167445099 / 160000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18110680354 / 1000000000000) (-18110679834 / 1000000000000), orderedInterval (41836623854 / 1000000000000) (41836624375 / 1000000000000)))) (orderedInterval (-11138715485 / 1000000000000) (-11138715380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (44276964773921 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-43664872829 / 1000000000000) (-43664870249 / 1000000000000), orderedInterval (98354598519 / 1000000000000) (98354601099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (118934155453037 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63765201920 / 1000000000000) (-63765200961 / 1000000000000), orderedInterval (14916271786 / 1000000000000) (14916272745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (322929368043129 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28999375888 / 1000000000000) (28999400980 / 1000000000000), orderedInterval (-27167970508 / 1000000000000) (-27167945416 / 1000000000000)))) (orderedInterval (5808207622 / 1000000000000) (5808212078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (237868310906177 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15035009629 / 1000000000000) (15035009831 / 1000000000000), orderedInterval (-43786383924 / 1000000000000) (-43786383722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (407591405073221 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34381994607 / 1000000000000) (34381994629 / 1000000000000), orderedInterval (8176210899 / 1000000000000) (8176210921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (300229984197839 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32732664635 / 1000000000000) (-32732594993 / 1000000000000), orderedInterval (25042109375 / 1000000000000) (25042179017 / 1000000000000)))) (orderedInterval (5830462970 / 1000000000000) (5830466603 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks2_1 :
    compactCertificate386.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (460630003364897 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33115443830 / 1000000000000) (-33115441424 / 1000000000000), orderedInterval (3031687340 / 1000000000000) (3031689746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (265944856439513 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9005634328 / 1000000000000) (9005634329 / 1000000000000), orderedInterval (42811021066 / 1000000000000) (42811021067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (471923814638317 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2315249264 / 1000000000000) (2315249265 / 1000000000000), orderedInterval (32767394633 / 1000000000000) (32767394634 / 1000000000000)))) (orderedInterval (-32313128153 / 1000000000000) (-32313125557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (440932443982273 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28026459599 / 1000000000000) (-28026409603 / 1000000000000), orderedInterval (19249381452 / 1000000000000) (19249431448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (314670197720209 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39796464640 / 1000000000000) (-39796464607 / 1000000000000), orderedInterval (-5844056524 / 1000000000000) (-5844056491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (356802466359111 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23816293608 / 1000000000000) (23816293609 / 1000000000000), orderedInterval (29302007585 / 1000000000000) (29302007586 / 1000000000000)))) (orderedInterval (6831609873 / 1000000000000) (6831614106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (297464697923159 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39047502043 / 1000000000000) (39047512884 / 1000000000000), orderedInterval (-13742392419 / 1000000000000) (-13742381578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (262819081814339 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23321908078 / 1000000000000) (23321910726 / 1000000000000), orderedInterval (-37370580957 / 1000000000000) (-37370578309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (76175213775561 / 160000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21892401054 / 1000000000000) (-21892398138 / 1000000000000), orderedInterval (29312790891 / 1000000000000) (29312793807 / 1000000000000)))) (orderedInterval (3133273777 / 1000000000000) (3133274596 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks2_2 :
    compactCertificate386.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (210704650185067 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13206128806 / 1000000000000) (13206128807 / 1000000000000), orderedInterval (47332183826 / 1000000000000) (47332183827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (178616665451987 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45007338307 / 1000000000000) (-45007338306 / 1000000000000), orderedInterval (-28633696741 / 1000000000000) (-28633696740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (111770015802161 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51795878255 / 1000000000000) (51795976032 / 1000000000000), orderedInterval (-43473022219 / 1000000000000) (-43472924442 / 1000000000000)))) (orderedInterval (-174882887 / 1000000000000) (-174881885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (60110286228687 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (46004765624 / 1000000000000) (46004765625 / 1000000000000), orderedInterval (79420569293 / 1000000000000) (79420569294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (163211120227061 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31318191526 / 1000000000000) (-31318191525 / 1000000000000), orderedInterval (-46179562755 / 1000000000000) (-46179562754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (222850831322197 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11978087954 / 1000000000000) (11978088032 / 1000000000000), orderedInterval (-46302112259 / 1000000000000) (-46302112181 / 1000000000000)))) (orderedInterval (684171492 / 1000000000000) (684171528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (94229984197839 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53181794518 / 1000000000000) (-53181711907 / 1000000000000), orderedInterval (50985094842 / 1000000000000) (50985177452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (383039654271919 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32141878847 / 1000000000000) (32141952828 / 1000000000000), orderedInterval (-17253160089 / 1000000000000) (-17253086109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (255852737439521 / 800000000000) 2 (IntervalRat.scale (515 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7041100258 / 1000000000000) (7041100259 / 1000000000000), orderedInterval (44045853850 / 1000000000000) (44045853851 / 1000000000000)))) (orderedInterval (11180176601 / 1000000000000) (11180197719 / 1000000000000))) = true
  rfl'

theorem compactCertificate386_chunkChecks2 :
    compactCertificate386.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate386.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate386_chunkChecks2_0
    compactCertificate386_chunkChecks2_1 compactCertificate386_chunkChecks2_2

theorem compactCertificate386_chunkChecks3_0 :
    compactCertificate386.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (515 / 2) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31044726694 / 1000000000000) (31044726695 / 1000000000000), orderedInterval (38779592620 / 1000000000000) (38779592621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (151738667633803 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53546081974 / 1000000000000) (53546089406 / 1000000000000), orderedInterval (-22259235573 / 1000000000000) (-22259228142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (49069167445099 / 160000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18110680354 / 1000000000000) (-18110679834 / 1000000000000), orderedInterval (41836623854 / 1000000000000) (41836624375 / 1000000000000)))) (orderedInterval (-19391978876 / 1000000000000) (-19391978769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (44276964773921 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-43664872829 / 1000000000000) (-43664870249 / 1000000000000), orderedInterval (98354598519 / 1000000000000) (98354601099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (118934155453037 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63765201920 / 1000000000000) (-63765200961 / 1000000000000), orderedInterval (14916271786 / 1000000000000) (14916272745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (322929368043129 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28999375888 / 1000000000000) (28999400980 / 1000000000000), orderedInterval (-27167970508 / 1000000000000) (-27167945416 / 1000000000000)))) (orderedInterval (-7556923466 / 1000000000000) (-7556916497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (237868310906177 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15035009629 / 1000000000000) (15035009831 / 1000000000000), orderedInterval (-43786383924 / 1000000000000) (-43786383722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (407591405073221 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34381994607 / 1000000000000) (34381994629 / 1000000000000), orderedInterval (8176210899 / 1000000000000) (8176210921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (300229984197839 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32732664635 / 1000000000000) (-32732594993 / 1000000000000), orderedInterval (25042109375 / 1000000000000) (25042179017 / 1000000000000)))) (orderedInterval (57198739 / 1000000000000) (57204050 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate386_chunkChecks3_1 :
    compactCertificate386.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (460630003364897 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33115443830 / 1000000000000) (-33115441424 / 1000000000000), orderedInterval (3031687340 / 1000000000000) (3031689746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (265944856439513 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9005634328 / 1000000000000) (9005634329 / 1000000000000), orderedInterval (42811021066 / 1000000000000) (42811021067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (471923814638317 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2315249264 / 1000000000000) (2315249265 / 1000000000000), orderedInterval (32767394633 / 1000000000000) (32767394634 / 1000000000000)))) (orderedInterval (-56680686651 / 1000000000000) (-56680680867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (440932443982273 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28026459599 / 1000000000000) (-28026409603 / 1000000000000), orderedInterval (19249381452 / 1000000000000) (19249431448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (314670197720209 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39796464640 / 1000000000000) (-39796464607 / 1000000000000), orderedInterval (-5844056524 / 1000000000000) (-5844056491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (356802466359111 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23816293608 / 1000000000000) (23816293609 / 1000000000000), orderedInterval (29302007585 / 1000000000000) (29302007586 / 1000000000000)))) (orderedInterval (6121521554 / 1000000000000) (6121530573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (297464697923159 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39047502043 / 1000000000000) (39047512884 / 1000000000000), orderedInterval (-13742392419 / 1000000000000) (-13742381578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (262819081814339 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23321908078 / 1000000000000) (23321910726 / 1000000000000), orderedInterval (-37370580957 / 1000000000000) (-37370578309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (76175213775561 / 160000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21892401054 / 1000000000000) (-21892398138 / 1000000000000), orderedInterval (29312790891 / 1000000000000) (29312793807 / 1000000000000)))) (orderedInterval (-8719123425 / 1000000000000) (-8719122176 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate386_chunkChecks3_2 :
    compactCertificate386.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (210704650185067 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13206128806 / 1000000000000) (13206128807 / 1000000000000), orderedInterval (47332183826 / 1000000000000) (47332183827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (178616665451987 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45007338307 / 1000000000000) (-45007338306 / 1000000000000), orderedInterval (-28633696741 / 1000000000000) (-28633696740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (111770015802161 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51795878255 / 1000000000000) (51795976032 / 1000000000000), orderedInterval (-43473022219 / 1000000000000) (-43472924442 / 1000000000000)))) (orderedInterval (7268666699 / 1000000000000) (7268667267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (60110286228687 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (46004765624 / 1000000000000) (46004765625 / 1000000000000), orderedInterval (79420569293 / 1000000000000) (79420569294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (163211120227061 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31318191526 / 1000000000000) (-31318191525 / 1000000000000), orderedInterval (-46179562755 / 1000000000000) (-46179562754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (222850831322197 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11978087954 / 1000000000000) (11978088032 / 1000000000000), orderedInterval (-46302112259 / 1000000000000) (-46302112181 / 1000000000000)))) (orderedInterval (-4979728272 / 1000000000000) (-4979728235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (94229984197839 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53181794518 / 1000000000000) (-53181711907 / 1000000000000), orderedInterval (50985094842 / 1000000000000) (50985177452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (383039654271919 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32141878847 / 1000000000000) (32141952828 / 1000000000000), orderedInterval (-17253160089 / 1000000000000) (-17253086109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (255852737439521 / 800000000000) 3 (IntervalRat.scale (515 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7041100258 / 1000000000000) (7041100259 / 1000000000000), orderedInterval (44045853850 / 1000000000000) (44045853851 / 1000000000000)))) (orderedInterval (6731375955 / 1000000000000) (6731415027 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate386_chunkChecks3 :
    compactCertificate386.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate386.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate386_chunkChecks3_0
    compactCertificate386_chunkChecks3_1 compactCertificate386_chunkChecks3_2

theorem compactCertificate386_chunkChecks4_0 :
    compactCertificate386.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (515 / 2) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31044726694 / 1000000000000) (31044726695 / 1000000000000), orderedInterval (38779592620 / 1000000000000) (38779592621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (151738667633803 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53546081974 / 1000000000000) (53546089406 / 1000000000000), orderedInterval (-22259235573 / 1000000000000) (-22259228142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (49069167445099 / 160000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18110680354 / 1000000000000) (-18110679834 / 1000000000000), orderedInterval (41836623854 / 1000000000000) (41836624375 / 1000000000000)))) (orderedInterval (10464021375 / 1000000000000) (10464021490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (44276964773921 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-43664872829 / 1000000000000) (-43664870249 / 1000000000000), orderedInterval (98354598519 / 1000000000000) (98354601099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (118934155453037 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-63765201920 / 1000000000000) (-63765200961 / 1000000000000), orderedInterval (14916271786 / 1000000000000) (14916272745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (322929368043129 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28999375888 / 1000000000000) (28999400980 / 1000000000000), orderedInterval (-27167970508 / 1000000000000) (-27167945416 / 1000000000000)))) (orderedInterval (-12648529157 / 1000000000000) (-12648518215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (237868310906177 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15035009629 / 1000000000000) (15035009831 / 1000000000000), orderedInterval (-43786383924 / 1000000000000) (-43786383722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (407591405073221 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34381994607 / 1000000000000) (34381994629 / 1000000000000), orderedInterval (8176210899 / 1000000000000) (8176210921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (300229984197839 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32732664635 / 1000000000000) (-32732594993 / 1000000000000), orderedInterval (25042109375 / 1000000000000) (25042179017 / 1000000000000)))) (orderedInterval (-19822527279 / 1000000000000) (-19822519483 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate386_chunkChecks4_1 :
    compactCertificate386.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (460630003364897 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33115443830 / 1000000000000) (-33115441424 / 1000000000000), orderedInterval (3031687340 / 1000000000000) (3031689746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (265944856439513 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9005634328 / 1000000000000) (9005634329 / 1000000000000), orderedInterval (42811021066 / 1000000000000) (42811021067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (471923814638317 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2315249264 / 1000000000000) (2315249265 / 1000000000000), orderedInterval (32767394633 / 1000000000000) (32767394634 / 1000000000000)))) (orderedInterval (158463837461 / 1000000000000) (158463850396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (440932443982273 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28026459599 / 1000000000000) (-28026409603 / 1000000000000), orderedInterval (19249381452 / 1000000000000) (19249431448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (314670197720209 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39796464640 / 1000000000000) (-39796464607 / 1000000000000), orderedInterval (-5844056524 / 1000000000000) (-5844056491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (356802466359111 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23816293608 / 1000000000000) (23816293609 / 1000000000000), orderedInterval (29302007585 / 1000000000000) (29302007586 / 1000000000000)))) (orderedInterval (-11000726542 / 1000000000000) (-11000707268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (297464697923159 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39047502043 / 1000000000000) (39047512884 / 1000000000000), orderedInterval (-13742392419 / 1000000000000) (-13742381578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (262819081814339 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23321908078 / 1000000000000) (23321910726 / 1000000000000), orderedInterval (-37370580957 / 1000000000000) (-37370578309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (76175213775561 / 160000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21892401054 / 1000000000000) (-21892398138 / 1000000000000), orderedInterval (29312790891 / 1000000000000) (29312793807 / 1000000000000)))) (orderedInterval (-8058210513 / 1000000000000) (-8058208555 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate386_chunkChecks4_2 :
    compactCertificate386.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (210704650185067 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13206128806 / 1000000000000) (13206128807 / 1000000000000), orderedInterval (47332183826 / 1000000000000) (47332183827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (178616665451987 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45007338307 / 1000000000000) (-45007338306 / 1000000000000), orderedInterval (-28633696741 / 1000000000000) (-28633696740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (111770015802161 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51795878255 / 1000000000000) (51795976032 / 1000000000000), orderedInterval (-43473022219 / 1000000000000) (-43472924442 / 1000000000000)))) (orderedInterval (-781636339 / 1000000000000) (-781636004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (60110286228687 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (46004765624 / 1000000000000) (46004765625 / 1000000000000), orderedInterval (79420569293 / 1000000000000) (79420569294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (163211120227061 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31318191526 / 1000000000000) (-31318191525 / 1000000000000), orderedInterval (-46179562755 / 1000000000000) (-46179562754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (222850831322197 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11978087954 / 1000000000000) (11978088032 / 1000000000000), orderedInterval (-46302112259 / 1000000000000) (-46302112181 / 1000000000000)))) (orderedInterval (-944766646 / 1000000000000) (-944766607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (94229984197839 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53181794518 / 1000000000000) (-53181711907 / 1000000000000), orderedInterval (50985094842 / 1000000000000) (50985177452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (383039654271919 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32141878847 / 1000000000000) (32141952828 / 1000000000000), orderedInterval (-17253160089 / 1000000000000) (-17253086109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (255852737439521 / 800000000000) 4 (IntervalRat.scale (515 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7041100258 / 1000000000000) (7041100259 / 1000000000000), orderedInterval (44045853850 / 1000000000000) (44045853851 / 1000000000000)))) (orderedInterval (-34485814426 / 1000000000000) (-34485741749 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate386_chunkChecks4 :
    compactCertificate386.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate386.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate386_chunkChecks4_0
    compactCertificate386_chunkChecks4_1 compactCertificate386_chunkChecks4_2

theorem compactCertificate386_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate386.chunkCheck r b = true :=
  compactCertificate386.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate386_chunkChecks0
    · exact compactCertificate386_chunkChecks1
    · exact compactCertificate386_chunkChecks2
    · exact compactCertificate386_chunkChecks3
    · exact compactCertificate386_chunkChecks4)

theorem compactCertificate386_coefficient0 :
    compactCertificate386.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate386_coefficient1 :
    compactCertificate386.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate386_coefficient2 :
    compactCertificate386.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate386_coefficient3 :
    compactCertificate386.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate386_coefficient4 :
    compactCertificate386.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate386_coefficients : ∀ r : Fin 5,
    compactCertificate386.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate386_coefficient0
  · exact compactCertificate386_coefficient1
  · exact compactCertificate386_coefficient2
  · exact compactCertificate386_coefficient3
  · exact compactCertificate386_coefficient4

theorem compactCertificate386_lower : (1 : ℚ) ≤ compactCertificate386.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate386, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate386_proves {t : ℝ} (ht : t ∈ compactCertificate386.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate386.proves compactCertificate386_states compactCertificate386_chunks
    compactCertificate386_coefficients compactCertificate386_lower ht

end Erdos232
