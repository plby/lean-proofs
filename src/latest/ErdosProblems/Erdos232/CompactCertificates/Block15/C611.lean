/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate611 : CompactCertificate where
  left := 482
  right := 483
  center := 965 / 2
  grid := fun i =>
    match i.val with
    | 0 => 154
    | 1 => 113
    | 2 => 183
    | 3 => 33
    | 4 => 89
    | 5 => 241
    | 6 => 177
    | 7 => 304
    | 8 => 224
    | 9 => 344
    | 10 => 198
    | 11 => 352
    | 12 => 329
    | 13 => 235
    | 14 => 266
    | 15 => 222
    | 16 => 196
    | 17 => 284
    | 18 => 157
    | 19 => 133
    | 20 => 83
    | 21 => 45
    | 22 => 122
    | 23 => 166
    | 24 => 70
    | 25 => 286
    | _ => 191
  point := fun i =>
    match i.val with
    | 0 => 965 / 2
    | 1 => 284325852944893 / 800000000000
    | 2 => 91945138999069 / 160000000000
    | 3 => 82965574770551 / 800000000000
    | 4 => 222857203907147 / 800000000000
    | 5 => 605100660507999 / 800000000000
    | 6 => 445714407814487 / 800000000000
    | 7 => 763739234748851 / 800000000000
    | 8 => 562566863594009 / 800000000000
    | 9 => 863122239314807 / 800000000000
    | 10 => 498323857211903 / 800000000000
    | 11 => 884284429370827 / 800000000000
    | 12 => 826213220277463 / 800000000000
    | 13 => 589624739417479 / 800000000000
    | 14 => 668571611721441 / 800000000000
    | 15 => 557385307758929 / 800000000000
    | 16 => 492466823205509 / 800000000000
    | 17 => 142736080181391 / 160000000000
    | 18 => 394815509570077 / 800000000000
    | 19 => 334689479924597 / 800000000000
    | 20 => 209433136405991 / 800000000000
    | 21 => 112633837302297 / 800000000000
    | 22 => 305822778677891 / 800000000000
    | 23 => 417574858691107 / 800000000000
    | 24 => 176566863594009 / 800000000000
    | 25 => 717734497810489 / 800000000000
    | _ => 479413381804151 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-18052659293 / 1000000000000) (-18052658607 / 1000000000000), orderedInterval (31538876469 / 1000000000000) (31538877155 / 1000000000000))
    | 1 => (orderedInterval (-39328905117 / 1000000000000) (-39328905116 / 1000000000000), orderedInterval (-15580394383 / 1000000000000) (-15580394382 / 1000000000000))
    | 2 => (orderedInterval (-16850399865 / 1000000000000) (-16850399864 / 1000000000000), orderedInterval (-28688816994 / 1000000000000) (-28688816993 / 1000000000000))
    | 3 => (orderedInterval (-57209874468 / 1000000000000) (-57209874467 / 1000000000000), orderedInterval (-53256095568 / 1000000000000) (-53256095567 / 1000000000000))
    | 4 => (orderedInterval (11608886936 / 1000000000000) (11608887006 / 1000000000000), orderedInterval (-46394731140 / 1000000000000) (-46394731070 / 1000000000000))
    | 5 => (orderedInterval (-1079822795 / 1000000000000) (-1079822794 / 1000000000000), orderedInterval (-28990757300 / 1000000000000) (-28990757299 / 1000000000000))
    | 6 => (orderedInterval (-32338099212 / 1000000000000) (-32338081212 / 1000000000000), orderedInterval (9872694586 / 1000000000000) (9872712585 / 1000000000000))
    | 7 => (orderedInterval (10415114300 / 1000000000000) (10415114301 / 1000000000000), orderedInterval (23624412387 / 1000000000000) (23624412388 / 1000000000000))
    | 8 => (orderedInterval (8229606709 / 1000000000000) (8229606710 / 1000000000000), orderedInterval (28935139234 / 1000000000000) (28935139235 / 1000000000000))
    | 9 => (orderedInterval (-20696072501 / 1000000000000) (-20696066204 / 1000000000000), orderedInterval (12727091537 / 1000000000000) (12727097833 / 1000000000000))
    | 10 => (orderedInterval (31856614002 / 1000000000000) (31856616915 / 1000000000000), orderedInterval (-2703903161 / 1000000000000) (-2703900248 / 1000000000000))
    | 11 => (orderedInterval (7096884851 / 1000000000000) (7096884852 / 1000000000000), orderedInterval (22922222250 / 1000000000000) (22922222251 / 1000000000000))
    | 12 => (orderedInterval (798835813 / 1000000000000) (798835814 / 1000000000000), orderedInterval (-24815376292 / 1000000000000) (-24815376291 / 1000000000000))
    | 13 => (orderedInterval (12998049290 / 1000000000000) (12998049343 / 1000000000000), orderedInterval (-26368132517 / 1000000000000) (-26368132464 / 1000000000000))
    | 14 => (orderedInterval (20480562810 / 1000000000000) (20480562811 / 1000000000000), orderedInterval (18489464801 / 1000000000000) (18489464802 / 1000000000000))
    | 15 => (orderedInterval (2514597575 / 1000000000000) (2514597576 / 1000000000000), orderedInterval (30121278062 / 1000000000000) (30121278063 / 1000000000000))
    | 16 => (orderedInterval (18595208923 / 1000000000000) (18595208924 / 1000000000000), orderedInterval (26222105887 / 1000000000000) (26222105888 / 1000000000000))
    | 17 => (orderedInterval (16660845676 / 1000000000000) (16660845677 / 1000000000000), orderedInterval (20872116456 / 1000000000000) (20872116457 / 1000000000000))
    | 18 => (orderedInterval (-31582551242 / 1000000000000) (-31582551240 / 1000000000000), orderedInterval (-17070666007 / 1000000000000) (-17070666006 / 1000000000000))
    | 19 => (orderedInterval (-37740894249 / 1000000000000) (-37740894241 / 1000000000000), orderedInterval (-9820008639 / 1000000000000) (-9820008631 / 1000000000000))
    | 20 => (orderedInterval (-47738842534 / 1000000000000) (-47738840021 / 1000000000000), orderedInterval (12451659614 / 1000000000000) (12451662127 / 1000000000000))
    | 21 => (orderedInterval (-13697591624 / 1000000000000) (-13697591623 / 1000000000000), orderedInterval (-65785213217 / 1000000000000) (-65785213216 / 1000000000000))
    | 22 => (orderedInterval (-8537221743 / 1000000000000) (-8537221724 / 1000000000000), orderedInterval (39916642601 / 1000000000000) (39916642620 / 1000000000000))
    | 23 => (orderedInterval (33134718280 / 1000000000000) (33134718286 / 1000000000000), orderedInterval (11001914426 / 1000000000000) (11001914432 / 1000000000000))
    | 24 => (orderedInterval (53703550576 / 1000000000000) (53703550669 / 1000000000000), orderedInterval (-719366269 / 1000000000000) (-719366175 / 1000000000000))
    | 25 => (orderedInterval (-13743958536 / 1000000000000) (-13743958481 / 1000000000000), orderedInterval (22826329576 / 1000000000000) (22826329631 / 1000000000000))
    | _ => (orderedInterval (-251618523 / 1000000000000) (-251618522 / 1000000000000), orderedInterval (-32592247922 / 1000000000000) (-32592247921 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8510711962 / 1000000000000) (-8510711657 / 1000000000000)
      | 1 => orderedInterval (1121311493 / 1000000000000) (1121311554 / 1000000000000)
      | 2 => orderedInterval (-122350453 / 1000000000000) (-122350425 / 1000000000000)
      | 3 => orderedInterval (7046617930 / 1000000000000) (7046619456 / 1000000000000)
      | 4 => orderedInterval (1111067868 / 1000000000000) (1111067931 / 1000000000000)
      | 5 => orderedInterval (-608520835 / 1000000000000) (-608520789 / 1000000000000)
      | 6 => orderedInterval (5631793179 / 1000000000000) (5631793383 / 1000000000000)
      | 7 => orderedInterval (-2092796993 / 1000000000000) (-2092796934 / 1000000000000)
      | _ => orderedInterval (1489735504 / 1000000000000) (1489735642 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (10388930080 / 1000000000000) (10388930390 / 1000000000000)
      | 1 => orderedInterval (2376955638 / 1000000000000) (2376955706 / 1000000000000)
      | 2 => orderedInterval (-422562172 / 1000000000000) (-422562124 / 1000000000000)
      | 3 => orderedInterval (2149545231 / 1000000000000) (2149548407 / 1000000000000)
      | 4 => orderedInterval (-3011956931 / 1000000000000) (-3011956830 / 1000000000000)
      | 5 => orderedInterval (-424158220 / 1000000000000) (-424158153 / 1000000000000)
      | 6 => orderedInterval (3493676210 / 1000000000000) (3493676367 / 1000000000000)
      | 7 => orderedInterval (-1275172351 / 1000000000000) (-1275172297 / 1000000000000)
      | _ => orderedInterval (4138092075 / 1000000000000) (4138092271 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (8735339724 / 1000000000000) (8735340040 / 1000000000000)
      | 1 => orderedInterval (-363530103 / 1000000000000) (-363530011 / 1000000000000)
      | 2 => orderedInterval (836030221 / 1000000000000) (836030305 / 1000000000000)
      | 3 => orderedInterval (-27620229183 / 1000000000000) (-27620222373 / 1000000000000)
      | 4 => orderedInterval (-2484731693 / 1000000000000) (-2484731527 / 1000000000000)
      | 5 => orderedInterval (214188290 / 1000000000000) (214188390 / 1000000000000)
      | 6 => orderedInterval (-6438794332 / 1000000000000) (-6438794200 / 1000000000000)
      | 7 => orderedInterval (2831375835 / 1000000000000) (2831375888 / 1000000000000)
      | _ => orderedInterval (-4017251056 / 1000000000000) (-4017250763 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9616839923 / 1000000000000) (-9616839599 / 1000000000000)
      | 1 => orderedInterval (-7618357065 / 1000000000000) (-7618356928 / 1000000000000)
      | 2 => orderedInterval (3477653284 / 1000000000000) (3477653437 / 1000000000000)
      | 3 => orderedInterval (-13405305787 / 1000000000000) (-13405290940 / 1000000000000)
      | 4 => orderedInterval (4985272207 / 1000000000000) (4985272487 / 1000000000000)
      | 5 => orderedInterval (-1309192535 / 1000000000000) (-1309192381 / 1000000000000)
      | 6 => orderedInterval (-3334489534 / 1000000000000) (-3334489417 / 1000000000000)
      | 7 => orderedInterval (1481799614 / 1000000000000) (1481799668 / 1000000000000)
      | _ => orderedInterval (238187218 / 1000000000000) (238187674 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9212974391 / 1000000000000) (-9212974059 / 1000000000000)
      | 1 => orderedInterval (543572423 / 1000000000000) (543572634 / 1000000000000)
      | 2 => orderedInterval (-4040458989 / 1000000000000) (-4040458707 / 1000000000000)
      | 3 => orderedInterval (126335514904 / 1000000000000) (126335547666 / 1000000000000)
      | 4 => orderedInterval (5435767910 / 1000000000000) (5435768393 / 1000000000000)
      | 5 => orderedInterval (2297322537 / 1000000000000) (2297322781 / 1000000000000)
      | 6 => orderedInterval (6613665289 / 1000000000000) (6613665399 / 1000000000000)
      | 7 => orderedInterval (-3405906914 / 1000000000000) (-3405906857 / 1000000000000)
      | _ => orderedInterval (13499213727 / 1000000000000) (13499214468 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (5066145731 / 1000000000000) (5066148161 / 1000000000000)
    | 1 => orderedInterval (17413349560 / 1000000000000) (17413353737 / 1000000000000)
    | 2 => orderedInterval (-28307602297 / 1000000000000) (-28307594251 / 1000000000000)
    | 3 => orderedInterval (-25101272521 / 1000000000000) (-25101255999 / 1000000000000)
    | _ => orderedInterval (138065716496 / 1000000000000) (138065751718 / 1000000000000)

theorem compactCertificate611_stateChecks0 :
    compactCertificate611.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (965 / 2)) (orderedInterval (-18052659293 / 1000000000000) (-18052658607 / 1000000000000), orderedInterval (31538876469 / 1000000000000) (31538877155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (284325852944893 / 800000000000)) (orderedInterval (-39328905117 / 1000000000000) (-39328905116 / 1000000000000), orderedInterval (-15580394383 / 1000000000000) (-15580394382 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (91945138999069 / 160000000000)) (orderedInterval (-16850399865 / 1000000000000) (-16850399864 / 1000000000000), orderedInterval (-28688816994 / 1000000000000) (-28688816993 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_stateChecks1 :
    compactCertificate611.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (82965574770551 / 800000000000)) (orderedInterval (-57209874468 / 1000000000000) (-57209874467 / 1000000000000), orderedInterval (-53256095568 / 1000000000000) (-53256095567 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (222857203907147 / 800000000000)) (orderedInterval (11608886936 / 1000000000000) (11608887006 / 1000000000000), orderedInterval (-46394731140 / 1000000000000) (-46394731070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (605100660507999 / 800000000000)) (orderedInterval (-1079822795 / 1000000000000) (-1079822794 / 1000000000000), orderedInterval (-28990757300 / 1000000000000) (-28990757299 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_stateChecks2 :
    compactCertificate611.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (445714407814487 / 800000000000)) (orderedInterval (-32338099212 / 1000000000000) (-32338081212 / 1000000000000), orderedInterval (9872694586 / 1000000000000) (9872712585 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 304 12 (763739234748851 / 800000000000)) (orderedInterval (10415114300 / 1000000000000) (10415114301 / 1000000000000), orderedInterval (23624412387 / 1000000000000) (23624412388 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (562566863594009 / 800000000000)) (orderedInterval (8229606709 / 1000000000000) (8229606710 / 1000000000000), orderedInterval (28935139234 / 1000000000000) (28935139235 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_stateChecks3 :
    compactCertificate611.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 344 12 (863122239314807 / 800000000000)) (orderedInterval (-20696072501 / 1000000000000) (-20696066204 / 1000000000000), orderedInterval (12727091537 / 1000000000000) (12727097833 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (498323857211903 / 800000000000)) (orderedInterval (31856614002 / 1000000000000) (31856616915 / 1000000000000), orderedInterval (-2703903161 / 1000000000000) (-2703900248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 352 12 (884284429370827 / 800000000000)) (orderedInterval (7096884851 / 1000000000000) (7096884852 / 1000000000000), orderedInterval (22922222250 / 1000000000000) (22922222251 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_stateChecks4 :
    compactCertificate611.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 329 12 (826213220277463 / 800000000000)) (orderedInterval (798835813 / 1000000000000) (798835814 / 1000000000000), orderedInterval (-24815376292 / 1000000000000) (-24815376291 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (589624739417479 / 800000000000)) (orderedInterval (12998049290 / 1000000000000) (12998049343 / 1000000000000), orderedInterval (-26368132517 / 1000000000000) (-26368132464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (668571611721441 / 800000000000)) (orderedInterval (20480562810 / 1000000000000) (20480562811 / 1000000000000), orderedInterval (18489464801 / 1000000000000) (18489464802 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_stateChecks5 :
    compactCertificate611.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (557385307758929 / 800000000000)) (orderedInterval (2514597575 / 1000000000000) (2514597576 / 1000000000000), orderedInterval (30121278062 / 1000000000000) (30121278063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (492466823205509 / 800000000000)) (orderedInterval (18595208923 / 1000000000000) (18595208924 / 1000000000000), orderedInterval (26222105887 / 1000000000000) (26222105888 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 284 12 (142736080181391 / 160000000000)) (orderedInterval (16660845676 / 1000000000000) (16660845677 / 1000000000000), orderedInterval (20872116456 / 1000000000000) (20872116457 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_stateChecks6 :
    compactCertificate611.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (394815509570077 / 800000000000)) (orderedInterval (-31582551242 / 1000000000000) (-31582551240 / 1000000000000), orderedInterval (-17070666007 / 1000000000000) (-17070666006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (334689479924597 / 800000000000)) (orderedInterval (-37740894249 / 1000000000000) (-37740894241 / 1000000000000), orderedInterval (-9820008639 / 1000000000000) (-9820008631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (209433136405991 / 800000000000)) (orderedInterval (-47738842534 / 1000000000000) (-47738840021 / 1000000000000), orderedInterval (12451659614 / 1000000000000) (12451662127 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_stateChecks7 :
    compactCertificate611.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (112633837302297 / 800000000000)) (orderedInterval (-13697591624 / 1000000000000) (-13697591623 / 1000000000000), orderedInterval (-65785213217 / 1000000000000) (-65785213216 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (305822778677891 / 800000000000)) (orderedInterval (-8537221743 / 1000000000000) (-8537221724 / 1000000000000), orderedInterval (39916642601 / 1000000000000) (39916642620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (417574858691107 / 800000000000)) (orderedInterval (33134718280 / 1000000000000) (33134718286 / 1000000000000), orderedInterval (11001914426 / 1000000000000) (11001914432 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_stateChecks8 :
    compactCertificate611.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176566863594009 / 800000000000)) (orderedInterval (53703550576 / 1000000000000) (53703550669 / 1000000000000), orderedInterval (-719366269 / 1000000000000) (-719366175 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (717734497810489 / 800000000000)) (orderedInterval (-13743958536 / 1000000000000) (-13743958481 / 1000000000000), orderedInterval (22826329576 / 1000000000000) (22826329631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (479413381804151 / 800000000000)) (orderedInterval (-251618523 / 1000000000000) (-251618522 / 1000000000000), orderedInterval (-32592247922 / 1000000000000) (-32592247921 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_states : ∀ j,
    BesselStateValid (compactCertificate611.point j) (compactCertificate611.state j) :=
  compactCertificate611.statesValid_of_checks3 compactCertificate611_stateChecks0
    compactCertificate611_stateChecks1 compactCertificate611_stateChecks2
    compactCertificate611_stateChecks3 compactCertificate611_stateChecks4
    compactCertificate611_stateChecks5 compactCertificate611_stateChecks6
    compactCertificate611_stateChecks7 compactCertificate611_stateChecks8

theorem compactCertificate611_chunkChecks0_0 :
    compactCertificate611.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (965 / 2) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18052659293 / 1000000000000) (-18052658607 / 1000000000000), orderedInterval (31538876469 / 1000000000000) (31538877155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (284325852944893 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39328905117 / 1000000000000) (-39328905116 / 1000000000000), orderedInterval (-15580394383 / 1000000000000) (-15580394382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (91945138999069 / 160000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-16850399865 / 1000000000000) (-16850399864 / 1000000000000), orderedInterval (-28688816994 / 1000000000000) (-28688816993 / 1000000000000)))) (orderedInterval (-8510711962 / 1000000000000) (-8510711657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (82965574770551 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-57209874468 / 1000000000000) (-57209874467 / 1000000000000), orderedInterval (-53256095568 / 1000000000000) (-53256095567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (222857203907147 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (11608886936 / 1000000000000) (11608887006 / 1000000000000), orderedInterval (-46394731140 / 1000000000000) (-46394731070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (605100660507999 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1079822795 / 1000000000000) (-1079822794 / 1000000000000), orderedInterval (-28990757300 / 1000000000000) (-28990757299 / 1000000000000)))) (orderedInterval (1121311493 / 1000000000000) (1121311554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (445714407814487 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32338099212 / 1000000000000) (-32338081212 / 1000000000000), orderedInterval (9872694586 / 1000000000000) (9872712585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (763739234748851 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10415114300 / 1000000000000) (10415114301 / 1000000000000), orderedInterval (23624412387 / 1000000000000) (23624412388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (562566863594009 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8229606709 / 1000000000000) (8229606710 / 1000000000000), orderedInterval (28935139234 / 1000000000000) (28935139235 / 1000000000000)))) (orderedInterval (-122350453 / 1000000000000) (-122350425 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks0_1 :
    compactCertificate611.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (863122239314807 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20696072501 / 1000000000000) (-20696066204 / 1000000000000), orderedInterval (12727091537 / 1000000000000) (12727097833 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (498323857211903 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31856614002 / 1000000000000) (31856616915 / 1000000000000), orderedInterval (-2703903161 / 1000000000000) (-2703900248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (884284429370827 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7096884851 / 1000000000000) (7096884852 / 1000000000000), orderedInterval (22922222250 / 1000000000000) (22922222251 / 1000000000000)))) (orderedInterval (7046617930 / 1000000000000) (7046619456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (826213220277463 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (798835813 / 1000000000000) (798835814 / 1000000000000), orderedInterval (-24815376292 / 1000000000000) (-24815376291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (589624739417479 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12998049290 / 1000000000000) (12998049343 / 1000000000000), orderedInterval (-26368132517 / 1000000000000) (-26368132464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (668571611721441 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20480562810 / 1000000000000) (20480562811 / 1000000000000), orderedInterval (18489464801 / 1000000000000) (18489464802 / 1000000000000)))) (orderedInterval (1111067868 / 1000000000000) (1111067931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (557385307758929 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2514597575 / 1000000000000) (2514597576 / 1000000000000), orderedInterval (30121278062 / 1000000000000) (30121278063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (492466823205509 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18595208923 / 1000000000000) (18595208924 / 1000000000000), orderedInterval (26222105887 / 1000000000000) (26222105888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (142736080181391 / 160000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16660845676 / 1000000000000) (16660845677 / 1000000000000), orderedInterval (20872116456 / 1000000000000) (20872116457 / 1000000000000)))) (orderedInterval (-608520835 / 1000000000000) (-608520789 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks0_2 :
    compactCertificate611.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (394815509570077 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31582551242 / 1000000000000) (-31582551240 / 1000000000000), orderedInterval (-17070666007 / 1000000000000) (-17070666006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (334689479924597 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37740894249 / 1000000000000) (-37740894241 / 1000000000000), orderedInterval (-9820008639 / 1000000000000) (-9820008631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (209433136405991 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47738842534 / 1000000000000) (-47738840021 / 1000000000000), orderedInterval (12451659614 / 1000000000000) (12451662127 / 1000000000000)))) (orderedInterval (5631793179 / 1000000000000) (5631793383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (112633837302297 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-13697591624 / 1000000000000) (-13697591623 / 1000000000000), orderedInterval (-65785213217 / 1000000000000) (-65785213216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (305822778677891 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8537221743 / 1000000000000) (-8537221724 / 1000000000000), orderedInterval (39916642601 / 1000000000000) (39916642620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (417574858691107 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33134718280 / 1000000000000) (33134718286 / 1000000000000), orderedInterval (11001914426 / 1000000000000) (11001914432 / 1000000000000)))) (orderedInterval (-2092796993 / 1000000000000) (-2092796934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (176566863594009 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53703550576 / 1000000000000) (53703550669 / 1000000000000), orderedInterval (-719366269 / 1000000000000) (-719366175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (717734497810489 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13743958536 / 1000000000000) (-13743958481 / 1000000000000), orderedInterval (22826329576 / 1000000000000) (22826329631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (479413381804151 / 800000000000) 0 (IntervalRat.scale (965 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-251618523 / 1000000000000) (-251618522 / 1000000000000), orderedInterval (-32592247922 / 1000000000000) (-32592247921 / 1000000000000)))) (orderedInterval (1489735504 / 1000000000000) (1489735642 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks0 :
    compactCertificate611.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate611.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate611_chunkChecks0_0
    compactCertificate611_chunkChecks0_1 compactCertificate611_chunkChecks0_2

theorem compactCertificate611_chunkChecks1_0 :
    compactCertificate611.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (965 / 2) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18052659293 / 1000000000000) (-18052658607 / 1000000000000), orderedInterval (31538876469 / 1000000000000) (31538877155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (284325852944893 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39328905117 / 1000000000000) (-39328905116 / 1000000000000), orderedInterval (-15580394383 / 1000000000000) (-15580394382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (91945138999069 / 160000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-16850399865 / 1000000000000) (-16850399864 / 1000000000000), orderedInterval (-28688816994 / 1000000000000) (-28688816993 / 1000000000000)))) (orderedInterval (10388930080 / 1000000000000) (10388930390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (82965574770551 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-57209874468 / 1000000000000) (-57209874467 / 1000000000000), orderedInterval (-53256095568 / 1000000000000) (-53256095567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (222857203907147 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (11608886936 / 1000000000000) (11608887006 / 1000000000000), orderedInterval (-46394731140 / 1000000000000) (-46394731070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (605100660507999 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1079822795 / 1000000000000) (-1079822794 / 1000000000000), orderedInterval (-28990757300 / 1000000000000) (-28990757299 / 1000000000000)))) (orderedInterval (2376955638 / 1000000000000) (2376955706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (445714407814487 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32338099212 / 1000000000000) (-32338081212 / 1000000000000), orderedInterval (9872694586 / 1000000000000) (9872712585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (763739234748851 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10415114300 / 1000000000000) (10415114301 / 1000000000000), orderedInterval (23624412387 / 1000000000000) (23624412388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (562566863594009 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8229606709 / 1000000000000) (8229606710 / 1000000000000), orderedInterval (28935139234 / 1000000000000) (28935139235 / 1000000000000)))) (orderedInterval (-422562172 / 1000000000000) (-422562124 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks1_1 :
    compactCertificate611.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (863122239314807 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20696072501 / 1000000000000) (-20696066204 / 1000000000000), orderedInterval (12727091537 / 1000000000000) (12727097833 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (498323857211903 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31856614002 / 1000000000000) (31856616915 / 1000000000000), orderedInterval (-2703903161 / 1000000000000) (-2703900248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (884284429370827 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7096884851 / 1000000000000) (7096884852 / 1000000000000), orderedInterval (22922222250 / 1000000000000) (22922222251 / 1000000000000)))) (orderedInterval (2149545231 / 1000000000000) (2149548407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (826213220277463 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (798835813 / 1000000000000) (798835814 / 1000000000000), orderedInterval (-24815376292 / 1000000000000) (-24815376291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (589624739417479 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12998049290 / 1000000000000) (12998049343 / 1000000000000), orderedInterval (-26368132517 / 1000000000000) (-26368132464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (668571611721441 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20480562810 / 1000000000000) (20480562811 / 1000000000000), orderedInterval (18489464801 / 1000000000000) (18489464802 / 1000000000000)))) (orderedInterval (-3011956931 / 1000000000000) (-3011956830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (557385307758929 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2514597575 / 1000000000000) (2514597576 / 1000000000000), orderedInterval (30121278062 / 1000000000000) (30121278063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (492466823205509 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18595208923 / 1000000000000) (18595208924 / 1000000000000), orderedInterval (26222105887 / 1000000000000) (26222105888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (142736080181391 / 160000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16660845676 / 1000000000000) (16660845677 / 1000000000000), orderedInterval (20872116456 / 1000000000000) (20872116457 / 1000000000000)))) (orderedInterval (-424158220 / 1000000000000) (-424158153 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks1_2 :
    compactCertificate611.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (394815509570077 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31582551242 / 1000000000000) (-31582551240 / 1000000000000), orderedInterval (-17070666007 / 1000000000000) (-17070666006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (334689479924597 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37740894249 / 1000000000000) (-37740894241 / 1000000000000), orderedInterval (-9820008639 / 1000000000000) (-9820008631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (209433136405991 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47738842534 / 1000000000000) (-47738840021 / 1000000000000), orderedInterval (12451659614 / 1000000000000) (12451662127 / 1000000000000)))) (orderedInterval (3493676210 / 1000000000000) (3493676367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (112633837302297 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-13697591624 / 1000000000000) (-13697591623 / 1000000000000), orderedInterval (-65785213217 / 1000000000000) (-65785213216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (305822778677891 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8537221743 / 1000000000000) (-8537221724 / 1000000000000), orderedInterval (39916642601 / 1000000000000) (39916642620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (417574858691107 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33134718280 / 1000000000000) (33134718286 / 1000000000000), orderedInterval (11001914426 / 1000000000000) (11001914432 / 1000000000000)))) (orderedInterval (-1275172351 / 1000000000000) (-1275172297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (176566863594009 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53703550576 / 1000000000000) (53703550669 / 1000000000000), orderedInterval (-719366269 / 1000000000000) (-719366175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (717734497810489 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13743958536 / 1000000000000) (-13743958481 / 1000000000000), orderedInterval (22826329576 / 1000000000000) (22826329631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (479413381804151 / 800000000000) 1 (IntervalRat.scale (965 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-251618523 / 1000000000000) (-251618522 / 1000000000000), orderedInterval (-32592247922 / 1000000000000) (-32592247921 / 1000000000000)))) (orderedInterval (4138092075 / 1000000000000) (4138092271 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks1 :
    compactCertificate611.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate611.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate611_chunkChecks1_0
    compactCertificate611_chunkChecks1_1 compactCertificate611_chunkChecks1_2

theorem compactCertificate611_chunkChecks2_0 :
    compactCertificate611.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (965 / 2) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18052659293 / 1000000000000) (-18052658607 / 1000000000000), orderedInterval (31538876469 / 1000000000000) (31538877155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (284325852944893 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39328905117 / 1000000000000) (-39328905116 / 1000000000000), orderedInterval (-15580394383 / 1000000000000) (-15580394382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (91945138999069 / 160000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-16850399865 / 1000000000000) (-16850399864 / 1000000000000), orderedInterval (-28688816994 / 1000000000000) (-28688816993 / 1000000000000)))) (orderedInterval (8735339724 / 1000000000000) (8735340040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (82965574770551 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-57209874468 / 1000000000000) (-57209874467 / 1000000000000), orderedInterval (-53256095568 / 1000000000000) (-53256095567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (222857203907147 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (11608886936 / 1000000000000) (11608887006 / 1000000000000), orderedInterval (-46394731140 / 1000000000000) (-46394731070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (605100660507999 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1079822795 / 1000000000000) (-1079822794 / 1000000000000), orderedInterval (-28990757300 / 1000000000000) (-28990757299 / 1000000000000)))) (orderedInterval (-363530103 / 1000000000000) (-363530011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (445714407814487 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32338099212 / 1000000000000) (-32338081212 / 1000000000000), orderedInterval (9872694586 / 1000000000000) (9872712585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (763739234748851 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10415114300 / 1000000000000) (10415114301 / 1000000000000), orderedInterval (23624412387 / 1000000000000) (23624412388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (562566863594009 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8229606709 / 1000000000000) (8229606710 / 1000000000000), orderedInterval (28935139234 / 1000000000000) (28935139235 / 1000000000000)))) (orderedInterval (836030221 / 1000000000000) (836030305 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks2_1 :
    compactCertificate611.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (863122239314807 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20696072501 / 1000000000000) (-20696066204 / 1000000000000), orderedInterval (12727091537 / 1000000000000) (12727097833 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (498323857211903 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31856614002 / 1000000000000) (31856616915 / 1000000000000), orderedInterval (-2703903161 / 1000000000000) (-2703900248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (884284429370827 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7096884851 / 1000000000000) (7096884852 / 1000000000000), orderedInterval (22922222250 / 1000000000000) (22922222251 / 1000000000000)))) (orderedInterval (-27620229183 / 1000000000000) (-27620222373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (826213220277463 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (798835813 / 1000000000000) (798835814 / 1000000000000), orderedInterval (-24815376292 / 1000000000000) (-24815376291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (589624739417479 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12998049290 / 1000000000000) (12998049343 / 1000000000000), orderedInterval (-26368132517 / 1000000000000) (-26368132464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (668571611721441 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20480562810 / 1000000000000) (20480562811 / 1000000000000), orderedInterval (18489464801 / 1000000000000) (18489464802 / 1000000000000)))) (orderedInterval (-2484731693 / 1000000000000) (-2484731527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (557385307758929 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2514597575 / 1000000000000) (2514597576 / 1000000000000), orderedInterval (30121278062 / 1000000000000) (30121278063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (492466823205509 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18595208923 / 1000000000000) (18595208924 / 1000000000000), orderedInterval (26222105887 / 1000000000000) (26222105888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (142736080181391 / 160000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16660845676 / 1000000000000) (16660845677 / 1000000000000), orderedInterval (20872116456 / 1000000000000) (20872116457 / 1000000000000)))) (orderedInterval (214188290 / 1000000000000) (214188390 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks2_2 :
    compactCertificate611.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (394815509570077 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31582551242 / 1000000000000) (-31582551240 / 1000000000000), orderedInterval (-17070666007 / 1000000000000) (-17070666006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (334689479924597 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37740894249 / 1000000000000) (-37740894241 / 1000000000000), orderedInterval (-9820008639 / 1000000000000) (-9820008631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (209433136405991 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47738842534 / 1000000000000) (-47738840021 / 1000000000000), orderedInterval (12451659614 / 1000000000000) (12451662127 / 1000000000000)))) (orderedInterval (-6438794332 / 1000000000000) (-6438794200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (112633837302297 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-13697591624 / 1000000000000) (-13697591623 / 1000000000000), orderedInterval (-65785213217 / 1000000000000) (-65785213216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (305822778677891 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8537221743 / 1000000000000) (-8537221724 / 1000000000000), orderedInterval (39916642601 / 1000000000000) (39916642620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (417574858691107 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33134718280 / 1000000000000) (33134718286 / 1000000000000), orderedInterval (11001914426 / 1000000000000) (11001914432 / 1000000000000)))) (orderedInterval (2831375835 / 1000000000000) (2831375888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (176566863594009 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53703550576 / 1000000000000) (53703550669 / 1000000000000), orderedInterval (-719366269 / 1000000000000) (-719366175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (717734497810489 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13743958536 / 1000000000000) (-13743958481 / 1000000000000), orderedInterval (22826329576 / 1000000000000) (22826329631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (479413381804151 / 800000000000) 2 (IntervalRat.scale (965 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-251618523 / 1000000000000) (-251618522 / 1000000000000), orderedInterval (-32592247922 / 1000000000000) (-32592247921 / 1000000000000)))) (orderedInterval (-4017251056 / 1000000000000) (-4017250763 / 1000000000000))) = true
  rfl'

theorem compactCertificate611_chunkChecks2 :
    compactCertificate611.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate611.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate611_chunkChecks2_0
    compactCertificate611_chunkChecks2_1 compactCertificate611_chunkChecks2_2

theorem compactCertificate611_chunkChecks3_0 :
    compactCertificate611.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (965 / 2) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18052659293 / 1000000000000) (-18052658607 / 1000000000000), orderedInterval (31538876469 / 1000000000000) (31538877155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (284325852944893 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39328905117 / 1000000000000) (-39328905116 / 1000000000000), orderedInterval (-15580394383 / 1000000000000) (-15580394382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (91945138999069 / 160000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-16850399865 / 1000000000000) (-16850399864 / 1000000000000), orderedInterval (-28688816994 / 1000000000000) (-28688816993 / 1000000000000)))) (orderedInterval (-9616839923 / 1000000000000) (-9616839599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (82965574770551 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-57209874468 / 1000000000000) (-57209874467 / 1000000000000), orderedInterval (-53256095568 / 1000000000000) (-53256095567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (222857203907147 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (11608886936 / 1000000000000) (11608887006 / 1000000000000), orderedInterval (-46394731140 / 1000000000000) (-46394731070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (605100660507999 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1079822795 / 1000000000000) (-1079822794 / 1000000000000), orderedInterval (-28990757300 / 1000000000000) (-28990757299 / 1000000000000)))) (orderedInterval (-7618357065 / 1000000000000) (-7618356928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (445714407814487 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32338099212 / 1000000000000) (-32338081212 / 1000000000000), orderedInterval (9872694586 / 1000000000000) (9872712585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (763739234748851 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10415114300 / 1000000000000) (10415114301 / 1000000000000), orderedInterval (23624412387 / 1000000000000) (23624412388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (562566863594009 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8229606709 / 1000000000000) (8229606710 / 1000000000000), orderedInterval (28935139234 / 1000000000000) (28935139235 / 1000000000000)))) (orderedInterval (3477653284 / 1000000000000) (3477653437 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate611_chunkChecks3_1 :
    compactCertificate611.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (863122239314807 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20696072501 / 1000000000000) (-20696066204 / 1000000000000), orderedInterval (12727091537 / 1000000000000) (12727097833 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (498323857211903 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31856614002 / 1000000000000) (31856616915 / 1000000000000), orderedInterval (-2703903161 / 1000000000000) (-2703900248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (884284429370827 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7096884851 / 1000000000000) (7096884852 / 1000000000000), orderedInterval (22922222250 / 1000000000000) (22922222251 / 1000000000000)))) (orderedInterval (-13405305787 / 1000000000000) (-13405290940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (826213220277463 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (798835813 / 1000000000000) (798835814 / 1000000000000), orderedInterval (-24815376292 / 1000000000000) (-24815376291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (589624739417479 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12998049290 / 1000000000000) (12998049343 / 1000000000000), orderedInterval (-26368132517 / 1000000000000) (-26368132464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (668571611721441 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20480562810 / 1000000000000) (20480562811 / 1000000000000), orderedInterval (18489464801 / 1000000000000) (18489464802 / 1000000000000)))) (orderedInterval (4985272207 / 1000000000000) (4985272487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (557385307758929 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2514597575 / 1000000000000) (2514597576 / 1000000000000), orderedInterval (30121278062 / 1000000000000) (30121278063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (492466823205509 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18595208923 / 1000000000000) (18595208924 / 1000000000000), orderedInterval (26222105887 / 1000000000000) (26222105888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (142736080181391 / 160000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16660845676 / 1000000000000) (16660845677 / 1000000000000), orderedInterval (20872116456 / 1000000000000) (20872116457 / 1000000000000)))) (orderedInterval (-1309192535 / 1000000000000) (-1309192381 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate611_chunkChecks3_2 :
    compactCertificate611.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (394815509570077 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31582551242 / 1000000000000) (-31582551240 / 1000000000000), orderedInterval (-17070666007 / 1000000000000) (-17070666006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (334689479924597 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37740894249 / 1000000000000) (-37740894241 / 1000000000000), orderedInterval (-9820008639 / 1000000000000) (-9820008631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (209433136405991 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47738842534 / 1000000000000) (-47738840021 / 1000000000000), orderedInterval (12451659614 / 1000000000000) (12451662127 / 1000000000000)))) (orderedInterval (-3334489534 / 1000000000000) (-3334489417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (112633837302297 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-13697591624 / 1000000000000) (-13697591623 / 1000000000000), orderedInterval (-65785213217 / 1000000000000) (-65785213216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (305822778677891 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8537221743 / 1000000000000) (-8537221724 / 1000000000000), orderedInterval (39916642601 / 1000000000000) (39916642620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (417574858691107 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33134718280 / 1000000000000) (33134718286 / 1000000000000), orderedInterval (11001914426 / 1000000000000) (11001914432 / 1000000000000)))) (orderedInterval (1481799614 / 1000000000000) (1481799668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (176566863594009 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53703550576 / 1000000000000) (53703550669 / 1000000000000), orderedInterval (-719366269 / 1000000000000) (-719366175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (717734497810489 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13743958536 / 1000000000000) (-13743958481 / 1000000000000), orderedInterval (22826329576 / 1000000000000) (22826329631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (479413381804151 / 800000000000) 3 (IntervalRat.scale (965 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-251618523 / 1000000000000) (-251618522 / 1000000000000), orderedInterval (-32592247922 / 1000000000000) (-32592247921 / 1000000000000)))) (orderedInterval (238187218 / 1000000000000) (238187674 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate611_chunkChecks3 :
    compactCertificate611.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate611.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate611_chunkChecks3_0
    compactCertificate611_chunkChecks3_1 compactCertificate611_chunkChecks3_2

theorem compactCertificate611_chunkChecks4_0 :
    compactCertificate611.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (965 / 2) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18052659293 / 1000000000000) (-18052658607 / 1000000000000), orderedInterval (31538876469 / 1000000000000) (31538877155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (284325852944893 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39328905117 / 1000000000000) (-39328905116 / 1000000000000), orderedInterval (-15580394383 / 1000000000000) (-15580394382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (91945138999069 / 160000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-16850399865 / 1000000000000) (-16850399864 / 1000000000000), orderedInterval (-28688816994 / 1000000000000) (-28688816993 / 1000000000000)))) (orderedInterval (-9212974391 / 1000000000000) (-9212974059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (82965574770551 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-57209874468 / 1000000000000) (-57209874467 / 1000000000000), orderedInterval (-53256095568 / 1000000000000) (-53256095567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (222857203907147 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (11608886936 / 1000000000000) (11608887006 / 1000000000000), orderedInterval (-46394731140 / 1000000000000) (-46394731070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (605100660507999 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1079822795 / 1000000000000) (-1079822794 / 1000000000000), orderedInterval (-28990757300 / 1000000000000) (-28990757299 / 1000000000000)))) (orderedInterval (543572423 / 1000000000000) (543572634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (445714407814487 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32338099212 / 1000000000000) (-32338081212 / 1000000000000), orderedInterval (9872694586 / 1000000000000) (9872712585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (763739234748851 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10415114300 / 1000000000000) (10415114301 / 1000000000000), orderedInterval (23624412387 / 1000000000000) (23624412388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (562566863594009 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8229606709 / 1000000000000) (8229606710 / 1000000000000), orderedInterval (28935139234 / 1000000000000) (28935139235 / 1000000000000)))) (orderedInterval (-4040458989 / 1000000000000) (-4040458707 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate611_chunkChecks4_1 :
    compactCertificate611.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (863122239314807 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20696072501 / 1000000000000) (-20696066204 / 1000000000000), orderedInterval (12727091537 / 1000000000000) (12727097833 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (498323857211903 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31856614002 / 1000000000000) (31856616915 / 1000000000000), orderedInterval (-2703903161 / 1000000000000) (-2703900248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (884284429370827 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7096884851 / 1000000000000) (7096884852 / 1000000000000), orderedInterval (22922222250 / 1000000000000) (22922222251 / 1000000000000)))) (orderedInterval (126335514904 / 1000000000000) (126335547666 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (826213220277463 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (798835813 / 1000000000000) (798835814 / 1000000000000), orderedInterval (-24815376292 / 1000000000000) (-24815376291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (589624739417479 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12998049290 / 1000000000000) (12998049343 / 1000000000000), orderedInterval (-26368132517 / 1000000000000) (-26368132464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (668571611721441 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20480562810 / 1000000000000) (20480562811 / 1000000000000), orderedInterval (18489464801 / 1000000000000) (18489464802 / 1000000000000)))) (orderedInterval (5435767910 / 1000000000000) (5435768393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (557385307758929 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2514597575 / 1000000000000) (2514597576 / 1000000000000), orderedInterval (30121278062 / 1000000000000) (30121278063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (492466823205509 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18595208923 / 1000000000000) (18595208924 / 1000000000000), orderedInterval (26222105887 / 1000000000000) (26222105888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (142736080181391 / 160000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16660845676 / 1000000000000) (16660845677 / 1000000000000), orderedInterval (20872116456 / 1000000000000) (20872116457 / 1000000000000)))) (orderedInterval (2297322537 / 1000000000000) (2297322781 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate611_chunkChecks4_2 :
    compactCertificate611.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (394815509570077 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31582551242 / 1000000000000) (-31582551240 / 1000000000000), orderedInterval (-17070666007 / 1000000000000) (-17070666006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (334689479924597 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37740894249 / 1000000000000) (-37740894241 / 1000000000000), orderedInterval (-9820008639 / 1000000000000) (-9820008631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (209433136405991 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47738842534 / 1000000000000) (-47738840021 / 1000000000000), orderedInterval (12451659614 / 1000000000000) (12451662127 / 1000000000000)))) (orderedInterval (6613665289 / 1000000000000) (6613665399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (112633837302297 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-13697591624 / 1000000000000) (-13697591623 / 1000000000000), orderedInterval (-65785213217 / 1000000000000) (-65785213216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (305822778677891 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8537221743 / 1000000000000) (-8537221724 / 1000000000000), orderedInterval (39916642601 / 1000000000000) (39916642620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (417574858691107 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33134718280 / 1000000000000) (33134718286 / 1000000000000), orderedInterval (11001914426 / 1000000000000) (11001914432 / 1000000000000)))) (orderedInterval (-3405906914 / 1000000000000) (-3405906857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (176566863594009 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53703550576 / 1000000000000) (53703550669 / 1000000000000), orderedInterval (-719366269 / 1000000000000) (-719366175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (717734497810489 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13743958536 / 1000000000000) (-13743958481 / 1000000000000), orderedInterval (22826329576 / 1000000000000) (22826329631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (479413381804151 / 800000000000) 4 (IntervalRat.scale (965 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-251618523 / 1000000000000) (-251618522 / 1000000000000), orderedInterval (-32592247922 / 1000000000000) (-32592247921 / 1000000000000)))) (orderedInterval (13499213727 / 1000000000000) (13499214468 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate611_chunkChecks4 :
    compactCertificate611.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate611.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate611_chunkChecks4_0
    compactCertificate611_chunkChecks4_1 compactCertificate611_chunkChecks4_2

theorem compactCertificate611_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate611.chunkCheck r b = true :=
  compactCertificate611.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate611_chunkChecks0
    · exact compactCertificate611_chunkChecks1
    · exact compactCertificate611_chunkChecks2
    · exact compactCertificate611_chunkChecks3
    · exact compactCertificate611_chunkChecks4)

theorem compactCertificate611_coefficient0 :
    compactCertificate611.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate611_coefficient1 :
    compactCertificate611.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate611_coefficient2 :
    compactCertificate611.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate611_coefficient3 :
    compactCertificate611.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate611_coefficient4 :
    compactCertificate611.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate611_coefficients : ∀ r : Fin 5,
    compactCertificate611.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate611_coefficient0
  · exact compactCertificate611_coefficient1
  · exact compactCertificate611_coefficient2
  · exact compactCertificate611_coefficient3
  · exact compactCertificate611_coefficient4

theorem compactCertificate611_lower : (1 : ℚ) ≤ compactCertificate611.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate611, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate611_proves {t : ℝ} (ht : t ∈ compactCertificate611.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate611.proves compactCertificate611_states compactCertificate611_chunks
    compactCertificate611_coefficients compactCertificate611_lower ht

end Erdos232
