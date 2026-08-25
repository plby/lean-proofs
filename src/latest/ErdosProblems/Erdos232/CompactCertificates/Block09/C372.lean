/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate372 : CompactCertificate where
  left := 243
  right := 244
  center := 487 / 2
  grid := fun i =>
    match i.val with
    | 0 => 78
    | 1 => 57
    | 2 => 92
    | 3 => 17
    | 4 => 45
    | 5 => 122
    | 6 => 90
    | 7 => 153
    | 8 => 113
    | 9 => 173
    | 10 => 100
    | 11 => 178
    | 12 => 166
    | 13 => 118
    | 14 => 134
    | 15 => 112
    | 16 => 99
    | 17 => 143
    | 18 => 79
    | 19 => 67
    | 20 => 42
    | 21 => 23
    | 22 => 61
    | 23 => 84
    | 24 => 35
    | 25 => 144
    | _ => 96
  point := fun i =>
    match i.val with
    | 0 => 487 / 2
    | 1 => 717443991627787 / 4000000000000
    | 2 => 232006646075371 / 800000000000
    | 3 => 209348367426209 / 4000000000000
    | 4 => 562339162190573 / 4000000000000
    | 5 => 1526860215893241 / 4000000000000
    | 6 => 1124678324381633 / 4000000000000
    | 7 => 1927155478355909 / 4000000000000
    | 8 => 1419534002954831 / 4000000000000
    | 9 => 2177930210084513 / 4000000000000
    | 10 => 1257428593068377 / 4000000000000
    | 11 => 2231329104163693 / 4000000000000
    | 12 => 2084797089508417 / 4000000000000
    | 13 => 1487809575628561 / 4000000000000
    | 14 => 1687017486571719 / 4000000000000
    | 15 => 1406459299889111 / 4000000000000
    | 16 => 1242649445083331 / 4000000000000
    | 17 => 360168243773769 / 800000000000
    | 18 => 996244316894443 / 4000000000000
    | 19 => 844527340535123 / 4000000000000
    | 20 => 528465997045169 / 4000000000000
    | 21 => 284210770809423 / 4000000000000
    | 22 => 771687529617269 / 4000000000000
    | 23 => 1053673348096213 / 4000000000000
    | 24 => 445534002954831 / 4000000000000
    | 25 => 1811070986703151 / 4000000000000
    | _ => 1209711486728609 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-35201341736 / 1000000000000) (-35201311080 / 1000000000000), orderedInterval (37157596956 / 1000000000000) (37157627612 / 1000000000000))
    | 1 => (orderedInterval (-52400603053 / 1000000000000) (-52400603052 / 1000000000000), orderedInterval (-28200813971 / 1000000000000) (-28200813970 / 1000000000000))
    | 2 => (orderedInterval (45956035999 / 1000000000000) (45956037543 / 1000000000000), orderedInterval (-9201588631 / 1000000000000) (-9201587087 / 1000000000000))
    | 3 => (orderedInterval (31216844761 / 1000000000000) (31216845317 / 1000000000000), orderedInterval (-106080099538 / 1000000000000) (-106080098982 / 1000000000000))
    | 4 => (orderedInterval (159472022 / 1000000000000) (159472028 / 1000000000000), orderedInterval (-67293746297 / 1000000000000) (-67293746292 / 1000000000000))
    | 5 => (orderedInterval (-28551432318 / 1000000000000) (-28551413984 / 1000000000000), orderedInterval (29236776655 / 1000000000000) (29236794989 / 1000000000000))
    | 6 => (orderedInterval (-33760970981 / 1000000000000) (-33760937269 / 1000000000000), orderedInterval (33591829175 / 1000000000000) (33591862887 / 1000000000000))
    | 7 => (orderedInterval (-34275326781 / 1000000000000) (-34275307749 / 1000000000000), orderedInterval (12142119741 / 1000000000000) (12142138773 / 1000000000000))
    | 8 => (orderedInterval (-26254118857 / 1000000000000) (-26254118856 / 1000000000000), orderedInterval (-33198615940 / 1000000000000) (-33198615939 / 1000000000000))
    | 9 => (orderedInterval (-33502737460 / 1000000000000) (-33502730806 / 1000000000000), orderedInterval (6870800967 / 1000000000000) (6870807620 / 1000000000000))
    | 10 => (orderedInterval (37445847767 / 1000000000000) (37445847768 / 1000000000000), orderedInterval (24899518658 / 1000000000000) (24899518659 / 1000000000000))
    | 11 => (orderedInterval (-18683863655 / 1000000000000) (-18683862696 / 1000000000000), orderedInterval (28161943412 / 1000000000000) (28161944372 / 1000000000000))
    | 12 => (orderedInterval (16140399905 / 1000000000000) (16140399906 / 1000000000000), orderedInterval (30983541586 / 1000000000000) (30983541587 / 1000000000000))
    | 13 => (orderedInterval (37093943223 / 1000000000000) (37093977545 / 1000000000000), orderedInterval (-18369259052 / 1000000000000) (-18369224730 / 1000000000000))
    | 14 => (orderedInterval (38851271353 / 1000000000000) (38851271652 / 1000000000000), orderedInterval (138038343 / 1000000000000) (138038642 / 1000000000000))
    | 15 => (orderedInterval (21931193975 / 1000000000000) (21931193976 / 1000000000000), orderedInterval (36432270557 / 1000000000000) (36432270558 / 1000000000000))
    | 16 => (orderedInterval (-18858099447 / 1000000000000) (-18858099446 / 1000000000000), orderedInterval (-41123111356 / 1000000000000) (-41123111355 / 1000000000000))
    | 17 => (orderedInterval (-37017131703 / 1000000000000) (-37017128609 / 1000000000000), orderedInterval (6657831404 / 1000000000000) (6657834498 / 1000000000000))
    | 18 => (orderedInterval (-50355907985 / 1000000000000) (-50355907658 / 1000000000000), orderedInterval (4612896545 / 1000000000000) (4612896872 / 1000000000000))
    | 19 => (orderedInterval (-54367524115 / 1000000000000) (-54367524106 / 1000000000000), orderedInterval (-7580693347 / 1000000000000) (-7580693338 / 1000000000000))
    | 20 => (orderedInterval (56627565974 / 1000000000000) (56627565975 / 1000000000000), orderedInterval (39934562351 / 1000000000000) (39934562352 / 1000000000000))
    | 21 => (orderedInterval (38622501943 / 1000000000000) (38622504344 / 1000000000000), orderedInterval (-86690964842 / 1000000000000) (-86690962441 / 1000000000000))
    | 22 => (orderedInterval (-50448504360 / 1000000000000) (-50448482837 / 1000000000000), orderedInterval (27604853769 / 1000000000000) (27604875291 / 1000000000000))
    | 23 => (orderedInterval (14972396200 / 1000000000000) (14972396201 / 1000000000000), orderedInterval (46796725725 / 1000000000000) (46796725726 / 1000000000000))
    | 24 => (orderedInterval (-60583335833 / 1000000000000) (-60583281696 / 1000000000000), orderedInterval (45495948351 / 1000000000000) (45496002488 / 1000000000000))
    | 25 => (orderedInterval (34430409496 / 1000000000000) (34430409498 / 1000000000000), orderedInterval (14814885465 / 1000000000000) (14814885467 / 1000000000000))
    | _ => (orderedInterval (45825134442 / 1000000000000) (45825134717 / 1000000000000), orderedInterval (-2330595796 / 1000000000000) (-2330595521 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11744098961 / 1000000000000) (-11744086701 / 1000000000000)
      | 1 => orderedInterval (1696851718 / 1000000000000) (1696853058 / 1000000000000)
      | 2 => orderedInterval (422677366 / 1000000000000) (422677967 / 1000000000000)
      | 3 => orderedInterval (6071438578 / 1000000000000) (6071439993 / 1000000000000)
      | 4 => orderedInterval (3019715727 / 1000000000000) (3019719004 / 1000000000000)
      | 5 => orderedInterval (384655755 / 1000000000000) (384655859 / 1000000000000)
      | 6 => orderedInterval (12972254242 / 1000000000000) (12972254357 / 1000000000000)
      | 7 => orderedInterval (-716118834 / 1000000000000) (-716118272 / 1000000000000)
      | _ => orderedInterval (-11765923646 / 1000000000000) (-11765923200 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13891318801 / 1000000000000) (13891331079 / 1000000000000)
      | 1 => orderedInterval (-4429377297 / 1000000000000) (-4429375219 / 1000000000000)
      | 2 => orderedInterval (-1910368799 / 1000000000000) (-1910367613 / 1000000000000)
      | 3 => orderedInterval (8823091924 / 1000000000000) (8823095081 / 1000000000000)
      | 4 => orderedInterval (-3851854217 / 1000000000000) (-3851849209 / 1000000000000)
      | 5 => orderedInterval (3925120594 / 1000000000000) (3925120775 / 1000000000000)
      | 6 => orderedInterval (323007977 / 1000000000000) (323008088 / 1000000000000)
      | 7 => orderedInterval (-3908906771 / 1000000000000) (-3908906344 / 1000000000000)
      | _ => orderedInterval (-1573816151 / 1000000000000) (-1573815842 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10335154600 / 1000000000000) (10335166952 / 1000000000000)
      | 1 => orderedInterval (-4955971153 / 1000000000000) (-4955967894 / 1000000000000)
      | 2 => orderedInterval (-2783133024 / 1000000000000) (-2783130679 / 1000000000000)
      | 3 => orderedInterval (-20486145772 / 1000000000000) (-20486138704 / 1000000000000)
      | 4 => orderedInterval (-6244033181 / 1000000000000) (-6244025504 / 1000000000000)
      | 5 => orderedInterval (939178910 / 1000000000000) (939179232 / 1000000000000)
      | 6 => orderedInterval (-11281002374 / 1000000000000) (-11281002264 / 1000000000000)
      | 7 => orderedInterval (701212411 / 1000000000000) (701212750 / 1000000000000)
      | _ => orderedInterval (23036058186 / 1000000000000) (23036058475 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13752960367 / 1000000000000) (-13752947987 / 1000000000000)
      | 1 => orderedInterval (8488462003 / 1000000000000) (8488467107 / 1000000000000)
      | 2 => orderedInterval (5396165598 / 1000000000000) (5396170231 / 1000000000000)
      | 3 => orderedInterval (-38368435798 / 1000000000000) (-38368419973 / 1000000000000)
      | 4 => orderedInterval (11705690646 / 1000000000000) (11705702385 / 1000000000000)
      | 5 => orderedInterval (-7235080783 / 1000000000000) (-7235080203 / 1000000000000)
      | 6 => orderedInterval (348244101 / 1000000000000) (348244210 / 1000000000000)
      | 7 => orderedInterval (4809267524 / 1000000000000) (4809267797 / 1000000000000)
      | _ => orderedInterval (6794195772 / 1000000000000) (6794196120 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8557095743 / 1000000000000) (-8557083279 / 1000000000000)
      | 1 => orderedInterval (12187432067 / 1000000000000) (12187440086 / 1000000000000)
      | 2 => orderedInterval (13295410170 / 1000000000000) (13295419347 / 1000000000000)
      | 3 => orderedInterval (83691260517 / 1000000000000) (83691296039 / 1000000000000)
      | 4 => orderedInterval (11115543134 / 1000000000000) (11115561143 / 1000000000000)
      | 5 => orderedInterval (-7055994583 / 1000000000000) (-7055993530 / 1000000000000)
      | 6 => orderedInterval (10708653745 / 1000000000000) (10708653855 / 1000000000000)
      | 7 => orderedInterval (-1165235525 / 1000000000000) (-1165235301 / 1000000000000)
      | _ => orderedInterval (-54033519946 / 1000000000000) (-54033519459 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (341451945 / 1000000000000) (341472065 / 1000000000000)
    | 1 => orderedInterval (11288216061 / 1000000000000) (11288240796 / 1000000000000)
    | 2 => orderedInterval (-10738681397 / 1000000000000) (-10738647636 / 1000000000000)
    | 3 => orderedInterval (-21814451304 / 1000000000000) (-21814400313 / 1000000000000)
    | _ => orderedInterval (60186453836 / 1000000000000) (60186538901 / 1000000000000)

theorem compactCertificate372_stateChecks0 :
    compactCertificate372.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (487 / 2)) (orderedInterval (-35201341736 / 1000000000000) (-35201311080 / 1000000000000), orderedInterval (37157596956 / 1000000000000) (37157627612 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717443991627787 / 4000000000000)) (orderedInterval (-52400603053 / 1000000000000) (-52400603052 / 1000000000000), orderedInterval (-28200813971 / 1000000000000) (-28200813970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (232006646075371 / 800000000000)) (orderedInterval (45956035999 / 1000000000000) (45956037543 / 1000000000000), orderedInterval (-9201588631 / 1000000000000) (-9201587087 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_stateChecks1 :
    compactCertificate372.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (209348367426209 / 4000000000000)) (orderedInterval (31216844761 / 1000000000000) (31216845317 / 1000000000000), orderedInterval (-106080099538 / 1000000000000) (-106080098982 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (562339162190573 / 4000000000000)) (orderedInterval (159472022 / 1000000000000) (159472028 / 1000000000000), orderedInterval (-67293746297 / 1000000000000) (-67293746292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1526860215893241 / 4000000000000)) (orderedInterval (-28551432318 / 1000000000000) (-28551413984 / 1000000000000), orderedInterval (29236776655 / 1000000000000) (29236794989 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_stateChecks2 :
    compactCertificate372.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1124678324381633 / 4000000000000)) (orderedInterval (-33760970981 / 1000000000000) (-33760937269 / 1000000000000), orderedInterval (33591829175 / 1000000000000) (33591862887 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1927155478355909 / 4000000000000)) (orderedInterval (-34275326781 / 1000000000000) (-34275307749 / 1000000000000), orderedInterval (12142119741 / 1000000000000) (12142138773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1419534002954831 / 4000000000000)) (orderedInterval (-26254118857 / 1000000000000) (-26254118856 / 1000000000000), orderedInterval (-33198615940 / 1000000000000) (-33198615939 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_stateChecks3 :
    compactCertificate372.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2177930210084513 / 4000000000000)) (orderedInterval (-33502737460 / 1000000000000) (-33502730806 / 1000000000000), orderedInterval (6870800967 / 1000000000000) (6870807620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1257428593068377 / 4000000000000)) (orderedInterval (37445847767 / 1000000000000) (37445847768 / 1000000000000), orderedInterval (24899518658 / 1000000000000) (24899518659 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2231329104163693 / 4000000000000)) (orderedInterval (-18683863655 / 1000000000000) (-18683862696 / 1000000000000), orderedInterval (28161943412 / 1000000000000) (28161944372 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_stateChecks4 :
    compactCertificate372.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2084797089508417 / 4000000000000)) (orderedInterval (16140399905 / 1000000000000) (16140399906 / 1000000000000), orderedInterval (30983541586 / 1000000000000) (30983541587 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1487809575628561 / 4000000000000)) (orderedInterval (37093943223 / 1000000000000) (37093977545 / 1000000000000), orderedInterval (-18369259052 / 1000000000000) (-18369224730 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1687017486571719 / 4000000000000)) (orderedInterval (38851271353 / 1000000000000) (38851271652 / 1000000000000), orderedInterval (138038343 / 1000000000000) (138038642 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_stateChecks5 :
    compactCertificate372.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1406459299889111 / 4000000000000)) (orderedInterval (21931193975 / 1000000000000) (21931193976 / 1000000000000), orderedInterval (36432270557 / 1000000000000) (36432270558 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1242649445083331 / 4000000000000)) (orderedInterval (-18858099447 / 1000000000000) (-18858099446 / 1000000000000), orderedInterval (-41123111356 / 1000000000000) (-41123111355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (360168243773769 / 800000000000)) (orderedInterval (-37017131703 / 1000000000000) (-37017128609 / 1000000000000), orderedInterval (6657831404 / 1000000000000) (6657834498 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_stateChecks6 :
    compactCertificate372.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (996244316894443 / 4000000000000)) (orderedInterval (-50355907985 / 1000000000000) (-50355907658 / 1000000000000), orderedInterval (4612896545 / 1000000000000) (4612896872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844527340535123 / 4000000000000)) (orderedInterval (-54367524115 / 1000000000000) (-54367524106 / 1000000000000), orderedInterval (-7580693347 / 1000000000000) (-7580693338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (528465997045169 / 4000000000000)) (orderedInterval (56627565974 / 1000000000000) (56627565975 / 1000000000000), orderedInterval (39934562351 / 1000000000000) (39934562352 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_stateChecks7 :
    compactCertificate372.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (284210770809423 / 4000000000000)) (orderedInterval (38622501943 / 1000000000000) (38622504344 / 1000000000000), orderedInterval (-86690964842 / 1000000000000) (-86690962441 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (771687529617269 / 4000000000000)) (orderedInterval (-50448504360 / 1000000000000) (-50448482837 / 1000000000000), orderedInterval (27604853769 / 1000000000000) (27604875291 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1053673348096213 / 4000000000000)) (orderedInterval (14972396200 / 1000000000000) (14972396201 / 1000000000000), orderedInterval (46796725725 / 1000000000000) (46796725726 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_stateChecks8 :
    compactCertificate372.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (445534002954831 / 4000000000000)) (orderedInterval (-60583335833 / 1000000000000) (-60583281696 / 1000000000000), orderedInterval (45495948351 / 1000000000000) (45496002488 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1811070986703151 / 4000000000000)) (orderedInterval (34430409496 / 1000000000000) (34430409498 / 1000000000000), orderedInterval (14814885465 / 1000000000000) (14814885467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1209711486728609 / 4000000000000)) (orderedInterval (45825134442 / 1000000000000) (45825134717 / 1000000000000), orderedInterval (-2330595796 / 1000000000000) (-2330595521 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_states : ∀ j,
    BesselStateValid (compactCertificate372.point j) (compactCertificate372.state j) :=
  compactCertificate372.statesValid_of_checks3 compactCertificate372_stateChecks0
    compactCertificate372_stateChecks1 compactCertificate372_stateChecks2
    compactCertificate372_stateChecks3 compactCertificate372_stateChecks4
    compactCertificate372_stateChecks5 compactCertificate372_stateChecks6
    compactCertificate372_stateChecks7 compactCertificate372_stateChecks8

theorem compactCertificate372_chunkChecks0_0 :
    compactCertificate372.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (487 / 2) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35201341736 / 1000000000000) (-35201311080 / 1000000000000), orderedInterval (37157596956 / 1000000000000) (37157627612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (717443991627787 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52400603053 / 1000000000000) (-52400603052 / 1000000000000), orderedInterval (-28200813971 / 1000000000000) (-28200813970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (232006646075371 / 800000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45956035999 / 1000000000000) (45956037543 / 1000000000000), orderedInterval (-9201588631 / 1000000000000) (-9201587087 / 1000000000000)))) (orderedInterval (-11744098961 / 1000000000000) (-11744086701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (209348367426209 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (31216844761 / 1000000000000) (31216845317 / 1000000000000), orderedInterval (-106080099538 / 1000000000000) (-106080098982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (562339162190573 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (159472022 / 1000000000000) (159472028 / 1000000000000), orderedInterval (-67293746297 / 1000000000000) (-67293746292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1526860215893241 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28551432318 / 1000000000000) (-28551413984 / 1000000000000), orderedInterval (29236776655 / 1000000000000) (29236794989 / 1000000000000)))) (orderedInterval (1696851718 / 1000000000000) (1696853058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1124678324381633 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33760970981 / 1000000000000) (-33760937269 / 1000000000000), orderedInterval (33591829175 / 1000000000000) (33591862887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1927155478355909 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34275326781 / 1000000000000) (-34275307749 / 1000000000000), orderedInterval (12142119741 / 1000000000000) (12142138773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1419534002954831 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26254118857 / 1000000000000) (-26254118856 / 1000000000000), orderedInterval (-33198615940 / 1000000000000) (-33198615939 / 1000000000000)))) (orderedInterval (422677366 / 1000000000000) (422677967 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks0_1 :
    compactCertificate372.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2177930210084513 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33502737460 / 1000000000000) (-33502730806 / 1000000000000), orderedInterval (6870800967 / 1000000000000) (6870807620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1257428593068377 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37445847767 / 1000000000000) (37445847768 / 1000000000000), orderedInterval (24899518658 / 1000000000000) (24899518659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2231329104163693 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18683863655 / 1000000000000) (-18683862696 / 1000000000000), orderedInterval (28161943412 / 1000000000000) (28161944372 / 1000000000000)))) (orderedInterval (6071438578 / 1000000000000) (6071439993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2084797089508417 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16140399905 / 1000000000000) (16140399906 / 1000000000000), orderedInterval (30983541586 / 1000000000000) (30983541587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1487809575628561 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37093943223 / 1000000000000) (37093977545 / 1000000000000), orderedInterval (-18369259052 / 1000000000000) (-18369224730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1687017486571719 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38851271353 / 1000000000000) (38851271652 / 1000000000000), orderedInterval (138038343 / 1000000000000) (138038642 / 1000000000000)))) (orderedInterval (3019715727 / 1000000000000) (3019719004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1406459299889111 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21931193975 / 1000000000000) (21931193976 / 1000000000000), orderedInterval (36432270557 / 1000000000000) (36432270558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1242649445083331 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18858099447 / 1000000000000) (-18858099446 / 1000000000000), orderedInterval (-41123111356 / 1000000000000) (-41123111355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (360168243773769 / 800000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37017131703 / 1000000000000) (-37017128609 / 1000000000000), orderedInterval (6657831404 / 1000000000000) (6657834498 / 1000000000000)))) (orderedInterval (384655755 / 1000000000000) (384655859 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks0_2 :
    compactCertificate372.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (996244316894443 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50355907985 / 1000000000000) (-50355907658 / 1000000000000), orderedInterval (4612896545 / 1000000000000) (4612896872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (844527340535123 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54367524115 / 1000000000000) (-54367524106 / 1000000000000), orderedInterval (-7580693347 / 1000000000000) (-7580693338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (528465997045169 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56627565974 / 1000000000000) (56627565975 / 1000000000000), orderedInterval (39934562351 / 1000000000000) (39934562352 / 1000000000000)))) (orderedInterval (12972254242 / 1000000000000) (12972254357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (284210770809423 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38622501943 / 1000000000000) (38622504344 / 1000000000000), orderedInterval (-86690964842 / 1000000000000) (-86690962441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (771687529617269 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50448504360 / 1000000000000) (-50448482837 / 1000000000000), orderedInterval (27604853769 / 1000000000000) (27604875291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1053673348096213 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14972396200 / 1000000000000) (14972396201 / 1000000000000), orderedInterval (46796725725 / 1000000000000) (46796725726 / 1000000000000)))) (orderedInterval (-716118834 / 1000000000000) (-716118272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (445534002954831 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60583335833 / 1000000000000) (-60583281696 / 1000000000000), orderedInterval (45495948351 / 1000000000000) (45496002488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1811070986703151 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34430409496 / 1000000000000) (34430409498 / 1000000000000), orderedInterval (14814885465 / 1000000000000) (14814885467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1209711486728609 / 4000000000000) 0 (IntervalRat.scale (487 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45825134442 / 1000000000000) (45825134717 / 1000000000000), orderedInterval (-2330595796 / 1000000000000) (-2330595521 / 1000000000000)))) (orderedInterval (-11765923646 / 1000000000000) (-11765923200 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks0 :
    compactCertificate372.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate372.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate372_chunkChecks0_0
    compactCertificate372_chunkChecks0_1 compactCertificate372_chunkChecks0_2

theorem compactCertificate372_chunkChecks1_0 :
    compactCertificate372.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (487 / 2) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35201341736 / 1000000000000) (-35201311080 / 1000000000000), orderedInterval (37157596956 / 1000000000000) (37157627612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (717443991627787 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52400603053 / 1000000000000) (-52400603052 / 1000000000000), orderedInterval (-28200813971 / 1000000000000) (-28200813970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (232006646075371 / 800000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45956035999 / 1000000000000) (45956037543 / 1000000000000), orderedInterval (-9201588631 / 1000000000000) (-9201587087 / 1000000000000)))) (orderedInterval (13891318801 / 1000000000000) (13891331079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (209348367426209 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (31216844761 / 1000000000000) (31216845317 / 1000000000000), orderedInterval (-106080099538 / 1000000000000) (-106080098982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (562339162190573 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (159472022 / 1000000000000) (159472028 / 1000000000000), orderedInterval (-67293746297 / 1000000000000) (-67293746292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1526860215893241 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28551432318 / 1000000000000) (-28551413984 / 1000000000000), orderedInterval (29236776655 / 1000000000000) (29236794989 / 1000000000000)))) (orderedInterval (-4429377297 / 1000000000000) (-4429375219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1124678324381633 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33760970981 / 1000000000000) (-33760937269 / 1000000000000), orderedInterval (33591829175 / 1000000000000) (33591862887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1927155478355909 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34275326781 / 1000000000000) (-34275307749 / 1000000000000), orderedInterval (12142119741 / 1000000000000) (12142138773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1419534002954831 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26254118857 / 1000000000000) (-26254118856 / 1000000000000), orderedInterval (-33198615940 / 1000000000000) (-33198615939 / 1000000000000)))) (orderedInterval (-1910368799 / 1000000000000) (-1910367613 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks1_1 :
    compactCertificate372.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2177930210084513 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33502737460 / 1000000000000) (-33502730806 / 1000000000000), orderedInterval (6870800967 / 1000000000000) (6870807620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1257428593068377 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37445847767 / 1000000000000) (37445847768 / 1000000000000), orderedInterval (24899518658 / 1000000000000) (24899518659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2231329104163693 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18683863655 / 1000000000000) (-18683862696 / 1000000000000), orderedInterval (28161943412 / 1000000000000) (28161944372 / 1000000000000)))) (orderedInterval (8823091924 / 1000000000000) (8823095081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2084797089508417 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16140399905 / 1000000000000) (16140399906 / 1000000000000), orderedInterval (30983541586 / 1000000000000) (30983541587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1487809575628561 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37093943223 / 1000000000000) (37093977545 / 1000000000000), orderedInterval (-18369259052 / 1000000000000) (-18369224730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1687017486571719 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38851271353 / 1000000000000) (38851271652 / 1000000000000), orderedInterval (138038343 / 1000000000000) (138038642 / 1000000000000)))) (orderedInterval (-3851854217 / 1000000000000) (-3851849209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1406459299889111 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21931193975 / 1000000000000) (21931193976 / 1000000000000), orderedInterval (36432270557 / 1000000000000) (36432270558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1242649445083331 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18858099447 / 1000000000000) (-18858099446 / 1000000000000), orderedInterval (-41123111356 / 1000000000000) (-41123111355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (360168243773769 / 800000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37017131703 / 1000000000000) (-37017128609 / 1000000000000), orderedInterval (6657831404 / 1000000000000) (6657834498 / 1000000000000)))) (orderedInterval (3925120594 / 1000000000000) (3925120775 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks1_2 :
    compactCertificate372.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (996244316894443 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50355907985 / 1000000000000) (-50355907658 / 1000000000000), orderedInterval (4612896545 / 1000000000000) (4612896872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (844527340535123 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54367524115 / 1000000000000) (-54367524106 / 1000000000000), orderedInterval (-7580693347 / 1000000000000) (-7580693338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (528465997045169 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56627565974 / 1000000000000) (56627565975 / 1000000000000), orderedInterval (39934562351 / 1000000000000) (39934562352 / 1000000000000)))) (orderedInterval (323007977 / 1000000000000) (323008088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (284210770809423 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38622501943 / 1000000000000) (38622504344 / 1000000000000), orderedInterval (-86690964842 / 1000000000000) (-86690962441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (771687529617269 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50448504360 / 1000000000000) (-50448482837 / 1000000000000), orderedInterval (27604853769 / 1000000000000) (27604875291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1053673348096213 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14972396200 / 1000000000000) (14972396201 / 1000000000000), orderedInterval (46796725725 / 1000000000000) (46796725726 / 1000000000000)))) (orderedInterval (-3908906771 / 1000000000000) (-3908906344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (445534002954831 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60583335833 / 1000000000000) (-60583281696 / 1000000000000), orderedInterval (45495948351 / 1000000000000) (45496002488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1811070986703151 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34430409496 / 1000000000000) (34430409498 / 1000000000000), orderedInterval (14814885465 / 1000000000000) (14814885467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1209711486728609 / 4000000000000) 1 (IntervalRat.scale (487 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45825134442 / 1000000000000) (45825134717 / 1000000000000), orderedInterval (-2330595796 / 1000000000000) (-2330595521 / 1000000000000)))) (orderedInterval (-1573816151 / 1000000000000) (-1573815842 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks1 :
    compactCertificate372.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate372.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate372_chunkChecks1_0
    compactCertificate372_chunkChecks1_1 compactCertificate372_chunkChecks1_2

theorem compactCertificate372_chunkChecks2_0 :
    compactCertificate372.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (487 / 2) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35201341736 / 1000000000000) (-35201311080 / 1000000000000), orderedInterval (37157596956 / 1000000000000) (37157627612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (717443991627787 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52400603053 / 1000000000000) (-52400603052 / 1000000000000), orderedInterval (-28200813971 / 1000000000000) (-28200813970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (232006646075371 / 800000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45956035999 / 1000000000000) (45956037543 / 1000000000000), orderedInterval (-9201588631 / 1000000000000) (-9201587087 / 1000000000000)))) (orderedInterval (10335154600 / 1000000000000) (10335166952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (209348367426209 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (31216844761 / 1000000000000) (31216845317 / 1000000000000), orderedInterval (-106080099538 / 1000000000000) (-106080098982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (562339162190573 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (159472022 / 1000000000000) (159472028 / 1000000000000), orderedInterval (-67293746297 / 1000000000000) (-67293746292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1526860215893241 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28551432318 / 1000000000000) (-28551413984 / 1000000000000), orderedInterval (29236776655 / 1000000000000) (29236794989 / 1000000000000)))) (orderedInterval (-4955971153 / 1000000000000) (-4955967894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1124678324381633 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33760970981 / 1000000000000) (-33760937269 / 1000000000000), orderedInterval (33591829175 / 1000000000000) (33591862887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1927155478355909 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34275326781 / 1000000000000) (-34275307749 / 1000000000000), orderedInterval (12142119741 / 1000000000000) (12142138773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1419534002954831 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26254118857 / 1000000000000) (-26254118856 / 1000000000000), orderedInterval (-33198615940 / 1000000000000) (-33198615939 / 1000000000000)))) (orderedInterval (-2783133024 / 1000000000000) (-2783130679 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks2_1 :
    compactCertificate372.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2177930210084513 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33502737460 / 1000000000000) (-33502730806 / 1000000000000), orderedInterval (6870800967 / 1000000000000) (6870807620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1257428593068377 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37445847767 / 1000000000000) (37445847768 / 1000000000000), orderedInterval (24899518658 / 1000000000000) (24899518659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2231329104163693 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18683863655 / 1000000000000) (-18683862696 / 1000000000000), orderedInterval (28161943412 / 1000000000000) (28161944372 / 1000000000000)))) (orderedInterval (-20486145772 / 1000000000000) (-20486138704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2084797089508417 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16140399905 / 1000000000000) (16140399906 / 1000000000000), orderedInterval (30983541586 / 1000000000000) (30983541587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1487809575628561 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37093943223 / 1000000000000) (37093977545 / 1000000000000), orderedInterval (-18369259052 / 1000000000000) (-18369224730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1687017486571719 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38851271353 / 1000000000000) (38851271652 / 1000000000000), orderedInterval (138038343 / 1000000000000) (138038642 / 1000000000000)))) (orderedInterval (-6244033181 / 1000000000000) (-6244025504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1406459299889111 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21931193975 / 1000000000000) (21931193976 / 1000000000000), orderedInterval (36432270557 / 1000000000000) (36432270558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1242649445083331 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18858099447 / 1000000000000) (-18858099446 / 1000000000000), orderedInterval (-41123111356 / 1000000000000) (-41123111355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (360168243773769 / 800000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37017131703 / 1000000000000) (-37017128609 / 1000000000000), orderedInterval (6657831404 / 1000000000000) (6657834498 / 1000000000000)))) (orderedInterval (939178910 / 1000000000000) (939179232 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks2_2 :
    compactCertificate372.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (996244316894443 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50355907985 / 1000000000000) (-50355907658 / 1000000000000), orderedInterval (4612896545 / 1000000000000) (4612896872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (844527340535123 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54367524115 / 1000000000000) (-54367524106 / 1000000000000), orderedInterval (-7580693347 / 1000000000000) (-7580693338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (528465997045169 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56627565974 / 1000000000000) (56627565975 / 1000000000000), orderedInterval (39934562351 / 1000000000000) (39934562352 / 1000000000000)))) (orderedInterval (-11281002374 / 1000000000000) (-11281002264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (284210770809423 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38622501943 / 1000000000000) (38622504344 / 1000000000000), orderedInterval (-86690964842 / 1000000000000) (-86690962441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (771687529617269 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50448504360 / 1000000000000) (-50448482837 / 1000000000000), orderedInterval (27604853769 / 1000000000000) (27604875291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1053673348096213 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14972396200 / 1000000000000) (14972396201 / 1000000000000), orderedInterval (46796725725 / 1000000000000) (46796725726 / 1000000000000)))) (orderedInterval (701212411 / 1000000000000) (701212750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (445534002954831 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60583335833 / 1000000000000) (-60583281696 / 1000000000000), orderedInterval (45495948351 / 1000000000000) (45496002488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1811070986703151 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34430409496 / 1000000000000) (34430409498 / 1000000000000), orderedInterval (14814885465 / 1000000000000) (14814885467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1209711486728609 / 4000000000000) 2 (IntervalRat.scale (487 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45825134442 / 1000000000000) (45825134717 / 1000000000000), orderedInterval (-2330595796 / 1000000000000) (-2330595521 / 1000000000000)))) (orderedInterval (23036058186 / 1000000000000) (23036058475 / 1000000000000))) = true
  rfl'

theorem compactCertificate372_chunkChecks2 :
    compactCertificate372.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate372.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate372_chunkChecks2_0
    compactCertificate372_chunkChecks2_1 compactCertificate372_chunkChecks2_2

theorem compactCertificate372_chunkChecks3_0 :
    compactCertificate372.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (487 / 2) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35201341736 / 1000000000000) (-35201311080 / 1000000000000), orderedInterval (37157596956 / 1000000000000) (37157627612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (717443991627787 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52400603053 / 1000000000000) (-52400603052 / 1000000000000), orderedInterval (-28200813971 / 1000000000000) (-28200813970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (232006646075371 / 800000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45956035999 / 1000000000000) (45956037543 / 1000000000000), orderedInterval (-9201588631 / 1000000000000) (-9201587087 / 1000000000000)))) (orderedInterval (-13752960367 / 1000000000000) (-13752947987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (209348367426209 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (31216844761 / 1000000000000) (31216845317 / 1000000000000), orderedInterval (-106080099538 / 1000000000000) (-106080098982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (562339162190573 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (159472022 / 1000000000000) (159472028 / 1000000000000), orderedInterval (-67293746297 / 1000000000000) (-67293746292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1526860215893241 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28551432318 / 1000000000000) (-28551413984 / 1000000000000), orderedInterval (29236776655 / 1000000000000) (29236794989 / 1000000000000)))) (orderedInterval (8488462003 / 1000000000000) (8488467107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1124678324381633 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33760970981 / 1000000000000) (-33760937269 / 1000000000000), orderedInterval (33591829175 / 1000000000000) (33591862887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1927155478355909 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34275326781 / 1000000000000) (-34275307749 / 1000000000000), orderedInterval (12142119741 / 1000000000000) (12142138773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1419534002954831 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26254118857 / 1000000000000) (-26254118856 / 1000000000000), orderedInterval (-33198615940 / 1000000000000) (-33198615939 / 1000000000000)))) (orderedInterval (5396165598 / 1000000000000) (5396170231 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate372_chunkChecks3_1 :
    compactCertificate372.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2177930210084513 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33502737460 / 1000000000000) (-33502730806 / 1000000000000), orderedInterval (6870800967 / 1000000000000) (6870807620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1257428593068377 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37445847767 / 1000000000000) (37445847768 / 1000000000000), orderedInterval (24899518658 / 1000000000000) (24899518659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2231329104163693 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18683863655 / 1000000000000) (-18683862696 / 1000000000000), orderedInterval (28161943412 / 1000000000000) (28161944372 / 1000000000000)))) (orderedInterval (-38368435798 / 1000000000000) (-38368419973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2084797089508417 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16140399905 / 1000000000000) (16140399906 / 1000000000000), orderedInterval (30983541586 / 1000000000000) (30983541587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1487809575628561 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37093943223 / 1000000000000) (37093977545 / 1000000000000), orderedInterval (-18369259052 / 1000000000000) (-18369224730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1687017486571719 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38851271353 / 1000000000000) (38851271652 / 1000000000000), orderedInterval (138038343 / 1000000000000) (138038642 / 1000000000000)))) (orderedInterval (11705690646 / 1000000000000) (11705702385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1406459299889111 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21931193975 / 1000000000000) (21931193976 / 1000000000000), orderedInterval (36432270557 / 1000000000000) (36432270558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1242649445083331 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18858099447 / 1000000000000) (-18858099446 / 1000000000000), orderedInterval (-41123111356 / 1000000000000) (-41123111355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (360168243773769 / 800000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37017131703 / 1000000000000) (-37017128609 / 1000000000000), orderedInterval (6657831404 / 1000000000000) (6657834498 / 1000000000000)))) (orderedInterval (-7235080783 / 1000000000000) (-7235080203 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate372_chunkChecks3_2 :
    compactCertificate372.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (996244316894443 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50355907985 / 1000000000000) (-50355907658 / 1000000000000), orderedInterval (4612896545 / 1000000000000) (4612896872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (844527340535123 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54367524115 / 1000000000000) (-54367524106 / 1000000000000), orderedInterval (-7580693347 / 1000000000000) (-7580693338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (528465997045169 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56627565974 / 1000000000000) (56627565975 / 1000000000000), orderedInterval (39934562351 / 1000000000000) (39934562352 / 1000000000000)))) (orderedInterval (348244101 / 1000000000000) (348244210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (284210770809423 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38622501943 / 1000000000000) (38622504344 / 1000000000000), orderedInterval (-86690964842 / 1000000000000) (-86690962441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (771687529617269 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50448504360 / 1000000000000) (-50448482837 / 1000000000000), orderedInterval (27604853769 / 1000000000000) (27604875291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1053673348096213 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14972396200 / 1000000000000) (14972396201 / 1000000000000), orderedInterval (46796725725 / 1000000000000) (46796725726 / 1000000000000)))) (orderedInterval (4809267524 / 1000000000000) (4809267797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (445534002954831 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60583335833 / 1000000000000) (-60583281696 / 1000000000000), orderedInterval (45495948351 / 1000000000000) (45496002488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1811070986703151 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34430409496 / 1000000000000) (34430409498 / 1000000000000), orderedInterval (14814885465 / 1000000000000) (14814885467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1209711486728609 / 4000000000000) 3 (IntervalRat.scale (487 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45825134442 / 1000000000000) (45825134717 / 1000000000000), orderedInterval (-2330595796 / 1000000000000) (-2330595521 / 1000000000000)))) (orderedInterval (6794195772 / 1000000000000) (6794196120 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate372_chunkChecks3 :
    compactCertificate372.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate372.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate372_chunkChecks3_0
    compactCertificate372_chunkChecks3_1 compactCertificate372_chunkChecks3_2

theorem compactCertificate372_chunkChecks4_0 :
    compactCertificate372.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (487 / 2) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35201341736 / 1000000000000) (-35201311080 / 1000000000000), orderedInterval (37157596956 / 1000000000000) (37157627612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (717443991627787 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52400603053 / 1000000000000) (-52400603052 / 1000000000000), orderedInterval (-28200813971 / 1000000000000) (-28200813970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (232006646075371 / 800000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45956035999 / 1000000000000) (45956037543 / 1000000000000), orderedInterval (-9201588631 / 1000000000000) (-9201587087 / 1000000000000)))) (orderedInterval (-8557095743 / 1000000000000) (-8557083279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (209348367426209 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (31216844761 / 1000000000000) (31216845317 / 1000000000000), orderedInterval (-106080099538 / 1000000000000) (-106080098982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (562339162190573 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (159472022 / 1000000000000) (159472028 / 1000000000000), orderedInterval (-67293746297 / 1000000000000) (-67293746292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1526860215893241 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28551432318 / 1000000000000) (-28551413984 / 1000000000000), orderedInterval (29236776655 / 1000000000000) (29236794989 / 1000000000000)))) (orderedInterval (12187432067 / 1000000000000) (12187440086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1124678324381633 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33760970981 / 1000000000000) (-33760937269 / 1000000000000), orderedInterval (33591829175 / 1000000000000) (33591862887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1927155478355909 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34275326781 / 1000000000000) (-34275307749 / 1000000000000), orderedInterval (12142119741 / 1000000000000) (12142138773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1419534002954831 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26254118857 / 1000000000000) (-26254118856 / 1000000000000), orderedInterval (-33198615940 / 1000000000000) (-33198615939 / 1000000000000)))) (orderedInterval (13295410170 / 1000000000000) (13295419347 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate372_chunkChecks4_1 :
    compactCertificate372.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2177930210084513 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33502737460 / 1000000000000) (-33502730806 / 1000000000000), orderedInterval (6870800967 / 1000000000000) (6870807620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1257428593068377 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37445847767 / 1000000000000) (37445847768 / 1000000000000), orderedInterval (24899518658 / 1000000000000) (24899518659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2231329104163693 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18683863655 / 1000000000000) (-18683862696 / 1000000000000), orderedInterval (28161943412 / 1000000000000) (28161944372 / 1000000000000)))) (orderedInterval (83691260517 / 1000000000000) (83691296039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2084797089508417 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16140399905 / 1000000000000) (16140399906 / 1000000000000), orderedInterval (30983541586 / 1000000000000) (30983541587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1487809575628561 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37093943223 / 1000000000000) (37093977545 / 1000000000000), orderedInterval (-18369259052 / 1000000000000) (-18369224730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1687017486571719 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38851271353 / 1000000000000) (38851271652 / 1000000000000), orderedInterval (138038343 / 1000000000000) (138038642 / 1000000000000)))) (orderedInterval (11115543134 / 1000000000000) (11115561143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1406459299889111 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21931193975 / 1000000000000) (21931193976 / 1000000000000), orderedInterval (36432270557 / 1000000000000) (36432270558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1242649445083331 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18858099447 / 1000000000000) (-18858099446 / 1000000000000), orderedInterval (-41123111356 / 1000000000000) (-41123111355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (360168243773769 / 800000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37017131703 / 1000000000000) (-37017128609 / 1000000000000), orderedInterval (6657831404 / 1000000000000) (6657834498 / 1000000000000)))) (orderedInterval (-7055994583 / 1000000000000) (-7055993530 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate372_chunkChecks4_2 :
    compactCertificate372.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (996244316894443 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50355907985 / 1000000000000) (-50355907658 / 1000000000000), orderedInterval (4612896545 / 1000000000000) (4612896872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (844527340535123 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54367524115 / 1000000000000) (-54367524106 / 1000000000000), orderedInterval (-7580693347 / 1000000000000) (-7580693338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (528465997045169 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (56627565974 / 1000000000000) (56627565975 / 1000000000000), orderedInterval (39934562351 / 1000000000000) (39934562352 / 1000000000000)))) (orderedInterval (10708653745 / 1000000000000) (10708653855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (284210770809423 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (38622501943 / 1000000000000) (38622504344 / 1000000000000), orderedInterval (-86690964842 / 1000000000000) (-86690962441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (771687529617269 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50448504360 / 1000000000000) (-50448482837 / 1000000000000), orderedInterval (27604853769 / 1000000000000) (27604875291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1053673348096213 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14972396200 / 1000000000000) (14972396201 / 1000000000000), orderedInterval (46796725725 / 1000000000000) (46796725726 / 1000000000000)))) (orderedInterval (-1165235525 / 1000000000000) (-1165235301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (445534002954831 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60583335833 / 1000000000000) (-60583281696 / 1000000000000), orderedInterval (45495948351 / 1000000000000) (45496002488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1811070986703151 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34430409496 / 1000000000000) (34430409498 / 1000000000000), orderedInterval (14814885465 / 1000000000000) (14814885467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1209711486728609 / 4000000000000) 4 (IntervalRat.scale (487 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45825134442 / 1000000000000) (45825134717 / 1000000000000), orderedInterval (-2330595796 / 1000000000000) (-2330595521 / 1000000000000)))) (orderedInterval (-54033519946 / 1000000000000) (-54033519459 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate372_chunkChecks4 :
    compactCertificate372.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate372.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate372_chunkChecks4_0
    compactCertificate372_chunkChecks4_1 compactCertificate372_chunkChecks4_2

theorem compactCertificate372_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate372.chunkCheck r b = true :=
  compactCertificate372.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate372_chunkChecks0
    · exact compactCertificate372_chunkChecks1
    · exact compactCertificate372_chunkChecks2
    · exact compactCertificate372_chunkChecks3
    · exact compactCertificate372_chunkChecks4)

theorem compactCertificate372_coefficient0 :
    compactCertificate372.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate372_coefficient1 :
    compactCertificate372.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate372_coefficient2 :
    compactCertificate372.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate372_coefficient3 :
    compactCertificate372.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate372_coefficient4 :
    compactCertificate372.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate372_coefficients : ∀ r : Fin 5,
    compactCertificate372.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate372_coefficient0
  · exact compactCertificate372_coefficient1
  · exact compactCertificate372_coefficient2
  · exact compactCertificate372_coefficient3
  · exact compactCertificate372_coefficient4

theorem compactCertificate372_lower : (1 : ℚ) ≤ compactCertificate372.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate372, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate372_proves {t : ℝ} (ht : t ∈ compactCertificate372.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate372.proves compactCertificate372_states compactCertificate372_chunks
    compactCertificate372_coefficients compactCertificate372_lower ht

end Erdos232
