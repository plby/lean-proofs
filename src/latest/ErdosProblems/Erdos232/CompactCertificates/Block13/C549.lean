/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate549 : CompactCertificate where
  left := 420
  right := 421
  center := 841 / 2
  grid := fun i =>
    match i.val with
    | 0 => 134
    | 1 => 99
    | 2 => 159
    | 3 => 29
    | 4 => 77
    | 5 => 210
    | 6 => 155
    | 7 => 265
    | 8 => 195
    | 9 => 299
    | 10 => 173
    | 11 => 307
    | 12 => 287
    | 13 => 205
    | 14 => 232
    | 15 => 193
    | 16 => 171
    | 17 => 248
    | 18 => 137
    | 19 => 116
    | 20 => 73
    | 21 => 39
    | 22 => 106
    | 23 => 145
    | 24 => 61
    | 25 => 249
    | _ => 166
  point := fun i =>
    match i.val with
    | 0 => 841 / 2
    | 1 => 1238953587184741 / 4000000000000
    | 2 => 400652134187653 / 800000000000
    | 3 => 361523566746287 / 4000000000000
    | 4 => 971103152776739 / 4000000000000
    | 5 => 2636733966255063 / 4000000000000
    | 6 => 1942206305554319 / 4000000000000
    | 7 => 3328003608413387 / 4000000000000
    | 8 => 2451392395246433 / 4000000000000
    | 9 => 3761066338154159 / 4000000000000
    | 10 => 2171452662773111 / 4000000000000
    | 11 => 3853280855444899 / 4000000000000
    | 12 => 3600234809602831 / 4000000000000
    | 13 => 2569297439637823 / 4000000000000
    | 14 => 2913309458330217 / 4000000000000
    | 15 => 2428813698576473 / 4000000000000
    | 16 => 2145930561221933 / 4000000000000
    | 17 => 621974318303367 / 800000000000
    | 18 => 1720413697142149 / 4000000000000
    | 19 => 1458413744127389 / 4000000000000
    | 20 => 912607604753567 / 4000000000000
    | 21 => 490803405032289 / 4000000000000
    | 22 => 1332626719523867 / 4000000000000
    | 23 => 1819587855747259 / 4000000000000
    | 24 => 769392395246433 / 4000000000000
    | 25 => 3127537371288193 / 4000000000000
    | _ => 2089050021229487 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (11932145852 / 1000000000000) (11932145853 / 1000000000000), orderedInterval (37020711663 / 1000000000000) (37020711664 / 1000000000000))
    | 1 => (orderedInterval (21507310278 / 1000000000000) (21507311707 / 1000000000000), orderedInterval (-39944413212 / 1000000000000) (-39944411783 / 1000000000000))
    | 2 => (orderedInterval (-31006317309 / 1000000000000) (-31006217341 / 1000000000000), orderedInterval (17631418629 / 1000000000000) (17631518596 / 1000000000000))
    | 3 => (orderedInterval (-4925320403 / 1000000000000) (-4925320400 / 1000000000000), orderedInterval (-83755754118 / 1000000000000) (-83755754115 / 1000000000000))
    | 4 => (orderedInterval (-51013146958 / 1000000000000) (-51013146653 / 1000000000000), orderedInterval (4566825581 / 1000000000000) (4566825886 / 1000000000000))
    | 5 => (orderedInterval (7213138653 / 1000000000000) (7213138654 / 1000000000000), orderedInterval (30222679166 / 1000000000000) (30222679167 / 1000000000000))
    | 6 => (orderedInterval (20747509895 / 1000000000000) (20747511837 / 1000000000000), orderedInterval (-29697416958 / 1000000000000) (-29697415016 / 1000000000000))
    | 7 => (orderedInterval (-7220729054 / 1000000000000) (-7220729053 / 1000000000000), orderedInterval (-26698251461 / 1000000000000) (-26698251460 / 1000000000000))
    | 8 => (orderedInterval (-27509521084 / 1000000000000) (-27509521083 / 1000000000000), orderedInterval (-16770856549 / 1000000000000) (-16770856548 / 1000000000000))
    | 9 => (orderedInterval (-25747949601 / 1000000000000) (-25747922504 / 1000000000000), orderedInterval (3769572471 / 1000000000000) (3769599568 / 1000000000000))
    | 10 => (orderedInterval (-5212422466 / 1000000000000) (-5212422465 / 1000000000000), orderedInterval (-33841007581 / 1000000000000) (-33841007580 / 1000000000000))
    | 11 => (orderedInterval (9139230579 / 1000000000000) (9139230582 / 1000000000000), orderedInterval (-24032529730 / 1000000000000) (-24032529727 / 1000000000000))
    | 12 => (orderedInterval (18950541114 / 1000000000000) (18950542537 / 1000000000000), orderedInterval (-18670274359 / 1000000000000) (-18670272936 / 1000000000000))
    | 13 => (orderedInterval (24988487277 / 1000000000000) (24988507570 / 1000000000000), orderedInterval (-19168710718 / 1000000000000) (-19168690425 / 1000000000000))
    | 14 => (orderedInterval (7688971103 / 1000000000000) (7688971104 / 1000000000000), orderedInterval (28542305543 / 1000000000000) (28542305544 / 1000000000000))
    | 15 => (orderedInterval (-32247377465 / 1000000000000) (-32247374596 / 1000000000000), orderedInterval (2950934389 / 1000000000000) (2950937258 / 1000000000000))
    | 16 => (orderedInterval (-1909557261 / 1000000000000) (-1909557260 / 1000000000000), orderedInterval (-34393118727 / 1000000000000) (-34393118726 / 1000000000000))
    | 17 => (orderedInterval (-21720287370 / 1000000000000) (-21720281397 / 1000000000000), orderedInterval (18643688925 / 1000000000000) (18643694897 / 1000000000000))
    | 18 => (orderedInterval (-18117764056 / 1000000000000) (-18117764055 / 1000000000000), orderedInterval (-33918623716 / 1000000000000) (-33918623715 / 1000000000000))
    | 19 => (orderedInterval (34320108779 / 1000000000000) (34320108780 / 1000000000000), orderedInterval (23789679310 / 1000000000000) (23789679311 / 1000000000000))
    | 20 => (orderedInterval (20546720592 / 1000000000000) (20546721349 / 1000000000000), orderedInterval (-48708874683 / 1000000000000) (-48708873926 / 1000000000000))
    | 21 => (orderedInterval (-59135000313 / 1000000000000) (-59135000312 / 1000000000000), orderedInterval (-40885981018 / 1000000000000) (-40885981017 / 1000000000000))
    | 22 => (orderedInterval (35116770761 / 1000000000000) (35116770762 / 1000000000000), orderedInterval (25979657455 / 1000000000000) (25979657456 / 1000000000000))
    | 23 => (orderedInterval (-5633053555 / 1000000000000) (-5633053554 / 1000000000000), orderedInterval (-36976923046 / 1000000000000) (-36976923045 / 1000000000000))
    | 24 => (orderedInterval (-57367969449 / 1000000000000) (-57367969428 / 1000000000000), orderedInterval (-4167404741 / 1000000000000) (-4167404720 / 1000000000000))
    | 25 => (orderedInterval (-11452806613 / 1000000000000) (-11452806612 / 1000000000000), orderedInterval (-26127816012 / 1000000000000) (-26127816011 / 1000000000000))
    | _ => (orderedInterval (34900459535 / 1000000000000) (34900459965 / 1000000000000), orderedInterval (927035547 / 1000000000000) (927035977 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (3110405253 / 1000000000000) (3110411163 / 1000000000000)
      | 1 => orderedInterval (-2321922293 / 1000000000000) (-2321922231 / 1000000000000)
      | 2 => orderedInterval (-442134686 / 1000000000000) (-442134662 / 1000000000000)
      | 3 => orderedInterval (5488092729 / 1000000000000) (5488097711 / 1000000000000)
      | 4 => orderedInterval (1981956552 / 1000000000000) (1981958547 / 1000000000000)
      | 5 => orderedInterval (-819229629 / 1000000000000) (-819229402 / 1000000000000)
      | 6 => orderedInterval (1623280896 / 1000000000000) (1623281026 / 1000000000000)
      | 7 => orderedInterval (726956201 / 1000000000000) (726956252 / 1000000000000)
      | _ => orderedInterval (-5961806279 / 1000000000000) (-5961806081 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15631795588 / 1000000000000) (15631802618 / 1000000000000)
      | 1 => orderedInterval (-3076478404 / 1000000000000) (-3076478340 / 1000000000000)
      | 2 => orderedInterval (1038616309 / 1000000000000) (1038616351 / 1000000000000)
      | 3 => orderedInterval (-12561234223 / 1000000000000) (-12561223111 / 1000000000000)
      | 4 => orderedInterval (-2297593045 / 1000000000000) (-2297589977 / 1000000000000)
      | 5 => orderedInterval (3442864316 / 1000000000000) (3442864705 / 1000000000000)
      | 6 => orderedInterval (3519308858 / 1000000000000) (3519308969 / 1000000000000)
      | 7 => orderedInterval (2819005776 / 1000000000000) (2819005822 / 1000000000000)
      | _ => orderedInterval (3727178109 / 1000000000000) (3727178373 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-2294499699 / 1000000000000) (-2294491315 / 1000000000000)
      | 1 => orderedInterval (1885825337 / 1000000000000) (1885825420 / 1000000000000)
      | 2 => orderedInterval (537834202 / 1000000000000) (537834276 / 1000000000000)
      | 3 => orderedInterval (-29020385907 / 1000000000000) (-29020361065 / 1000000000000)
      | 4 => orderedInterval (-3824025223 / 1000000000000) (-3824020485 / 1000000000000)
      | 5 => orderedInterval (2491511726 / 1000000000000) (2491512406 / 1000000000000)
      | 6 => orderedInterval (-1775600377 / 1000000000000) (-1775600276 / 1000000000000)
      | 7 => orderedInterval (-104808402 / 1000000000000) (-104808357 / 1000000000000)
      | _ => orderedInterval (6941368146 / 1000000000000) (6941368513 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16267339701 / 1000000000000) (-16267329721 / 1000000000000)
      | 1 => orderedInterval (8231143060 / 1000000000000) (8231143181 / 1000000000000)
      | 2 => orderedInterval (-5125146673 / 1000000000000) (-5125146540 / 1000000000000)
      | 3 => orderedInterval (54027630586 / 1000000000000) (54027686102 / 1000000000000)
      | 4 => orderedInterval (3914952080 / 1000000000000) (3914959411 / 1000000000000)
      | 5 => orderedInterval (-7212923472 / 1000000000000) (-7212922271 / 1000000000000)
      | 6 => orderedInterval (-4668187897 / 1000000000000) (-4668187802 / 1000000000000)
      | 7 => orderedInterval (-3313105556 / 1000000000000) (-3313105509 / 1000000000000)
      | _ => orderedInterval (-13353926388 / 1000000000000) (-13353925861 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (1204882812 / 1000000000000) (1204894719 / 1000000000000)
      | 1 => orderedInterval (-3342626235 / 1000000000000) (-3342626050 / 1000000000000)
      | 2 => orderedInterval (438089021 / 1000000000000) (438089267 / 1000000000000)
      | 3 => orderedInterval (148831822942 / 1000000000000) (148831947182 / 1000000000000)
      | 4 => orderedInterval (5315167404 / 1000000000000) (5315178820 / 1000000000000)
      | 5 => orderedInterval (-7794085375 / 1000000000000) (-7794083227 / 1000000000000)
      | 6 => orderedInterval (2152945261 / 1000000000000) (2152945352 / 1000000000000)
      | 7 => orderedInterval (301017082 / 1000000000000) (301017132 / 1000000000000)
      | _ => orderedInterval (-4389080757 / 1000000000000) (-4389079965 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (3385598744 / 1000000000000) (3385612323 / 1000000000000)
    | 1 => orderedInterval (12243463284 / 1000000000000) (12243485410 / 1000000000000)
    | 2 => orderedInterval (-25162780197 / 1000000000000) (-25162740883 / 1000000000000)
    | 3 => orderedInterval (16233096039 / 1000000000000) (16233170990 / 1000000000000)
    | _ => orderedInterval (142718132155 / 1000000000000) (142718283230 / 1000000000000)

theorem compactCertificate549_stateChecks0 :
    compactCertificate549.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (841 / 2)) (orderedInterval (11932145852 / 1000000000000) (11932145853 / 1000000000000), orderedInterval (37020711663 / 1000000000000) (37020711664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1238953587184741 / 4000000000000)) (orderedInterval (21507310278 / 1000000000000) (21507311707 / 1000000000000), orderedInterval (-39944413212 / 1000000000000) (-39944411783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (400652134187653 / 800000000000)) (orderedInterval (-31006317309 / 1000000000000) (-31006217341 / 1000000000000), orderedInterval (17631418629 / 1000000000000) (17631518596 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_stateChecks1 :
    compactCertificate549.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (361523566746287 / 4000000000000)) (orderedInterval (-4925320403 / 1000000000000) (-4925320400 / 1000000000000), orderedInterval (-83755754118 / 1000000000000) (-83755754115 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (971103152776739 / 4000000000000)) (orderedInterval (-51013146958 / 1000000000000) (-51013146653 / 1000000000000), orderedInterval (4566825581 / 1000000000000) (4566825886 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2636733966255063 / 4000000000000)) (orderedInterval (7213138653 / 1000000000000) (7213138654 / 1000000000000), orderedInterval (30222679166 / 1000000000000) (30222679167 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_stateChecks2 :
    compactCertificate549.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1942206305554319 / 4000000000000)) (orderedInterval (20747509895 / 1000000000000) (20747511837 / 1000000000000), orderedInterval (-29697416958 / 1000000000000) (-29697415016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (3328003608413387 / 4000000000000)) (orderedInterval (-7220729054 / 1000000000000) (-7220729053 / 1000000000000), orderedInterval (-26698251461 / 1000000000000) (-26698251460 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2451392395246433 / 4000000000000)) (orderedInterval (-27509521084 / 1000000000000) (-27509521083 / 1000000000000), orderedInterval (-16770856549 / 1000000000000) (-16770856548 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_stateChecks3 :
    compactCertificate549.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 299 12 (3761066338154159 / 4000000000000)) (orderedInterval (-25747949601 / 1000000000000) (-25747922504 / 1000000000000), orderedInterval (3769572471 / 1000000000000) (3769599568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2171452662773111 / 4000000000000)) (orderedInterval (-5212422466 / 1000000000000) (-5212422465 / 1000000000000), orderedInterval (-33841007581 / 1000000000000) (-33841007580 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 307 12 (3853280855444899 / 4000000000000)) (orderedInterval (9139230579 / 1000000000000) (9139230582 / 1000000000000), orderedInterval (-24032529730 / 1000000000000) (-24032529727 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_stateChecks4 :
    compactCertificate549.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (3600234809602831 / 4000000000000)) (orderedInterval (18950541114 / 1000000000000) (18950542537 / 1000000000000), orderedInterval (-18670274359 / 1000000000000) (-18670272936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2569297439637823 / 4000000000000)) (orderedInterval (24988487277 / 1000000000000) (24988507570 / 1000000000000), orderedInterval (-19168710718 / 1000000000000) (-19168690425 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2913309458330217 / 4000000000000)) (orderedInterval (7688971103 / 1000000000000) (7688971104 / 1000000000000), orderedInterval (28542305543 / 1000000000000) (28542305544 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_stateChecks5 :
    compactCertificate549.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2428813698576473 / 4000000000000)) (orderedInterval (-32247377465 / 1000000000000) (-32247374596 / 1000000000000), orderedInterval (2950934389 / 1000000000000) (2950937258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2145930561221933 / 4000000000000)) (orderedInterval (-1909557261 / 1000000000000) (-1909557260 / 1000000000000), orderedInterval (-34393118727 / 1000000000000) (-34393118726 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (621974318303367 / 800000000000)) (orderedInterval (-21720287370 / 1000000000000) (-21720281397 / 1000000000000), orderedInterval (18643688925 / 1000000000000) (18643694897 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_stateChecks6 :
    compactCertificate549.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1720413697142149 / 4000000000000)) (orderedInterval (-18117764056 / 1000000000000) (-18117764055 / 1000000000000), orderedInterval (-33918623716 / 1000000000000) (-33918623715 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1458413744127389 / 4000000000000)) (orderedInterval (34320108779 / 1000000000000) (34320108780 / 1000000000000), orderedInterval (23789679310 / 1000000000000) (23789679311 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (912607604753567 / 4000000000000)) (orderedInterval (20546720592 / 1000000000000) (20546721349 / 1000000000000), orderedInterval (-48708874683 / 1000000000000) (-48708873926 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_stateChecks7 :
    compactCertificate549.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (490803405032289 / 4000000000000)) (orderedInterval (-59135000313 / 1000000000000) (-59135000312 / 1000000000000), orderedInterval (-40885981018 / 1000000000000) (-40885981017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1332626719523867 / 4000000000000)) (orderedInterval (35116770761 / 1000000000000) (35116770762 / 1000000000000), orderedInterval (25979657455 / 1000000000000) (25979657456 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1819587855747259 / 4000000000000)) (orderedInterval (-5633053555 / 1000000000000) (-5633053554 / 1000000000000), orderedInterval (-36976923046 / 1000000000000) (-36976923045 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_stateChecks8 :
    compactCertificate549.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (769392395246433 / 4000000000000)) (orderedInterval (-57367969449 / 1000000000000) (-57367969428 / 1000000000000), orderedInterval (-4167404741 / 1000000000000) (-4167404720 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3127537371288193 / 4000000000000)) (orderedInterval (-11452806613 / 1000000000000) (-11452806612 / 1000000000000), orderedInterval (-26127816012 / 1000000000000) (-26127816011 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2089050021229487 / 4000000000000)) (orderedInterval (34900459535 / 1000000000000) (34900459965 / 1000000000000), orderedInterval (927035547 / 1000000000000) (927035977 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_states : ∀ j,
    BesselStateValid (compactCertificate549.point j) (compactCertificate549.state j) :=
  compactCertificate549.statesValid_of_checks3 compactCertificate549_stateChecks0
    compactCertificate549_stateChecks1 compactCertificate549_stateChecks2
    compactCertificate549_stateChecks3 compactCertificate549_stateChecks4
    compactCertificate549_stateChecks5 compactCertificate549_stateChecks6
    compactCertificate549_stateChecks7 compactCertificate549_stateChecks8

theorem compactCertificate549_chunkChecks0_0 :
    compactCertificate549.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (841 / 2) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932145852 / 1000000000000) (11932145853 / 1000000000000), orderedInterval (37020711663 / 1000000000000) (37020711664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1238953587184741 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21507310278 / 1000000000000) (21507311707 / 1000000000000), orderedInterval (-39944413212 / 1000000000000) (-39944411783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (400652134187653 / 800000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31006317309 / 1000000000000) (-31006217341 / 1000000000000), orderedInterval (17631418629 / 1000000000000) (17631518596 / 1000000000000)))) (orderedInterval (3110405253 / 1000000000000) (3110411163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (361523566746287 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4925320403 / 1000000000000) (-4925320400 / 1000000000000), orderedInterval (-83755754118 / 1000000000000) (-83755754115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (971103152776739 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51013146958 / 1000000000000) (-51013146653 / 1000000000000), orderedInterval (4566825581 / 1000000000000) (4566825886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2636733966255063 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7213138653 / 1000000000000) (7213138654 / 1000000000000), orderedInterval (30222679166 / 1000000000000) (30222679167 / 1000000000000)))) (orderedInterval (-2321922293 / 1000000000000) (-2321922231 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1942206305554319 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20747509895 / 1000000000000) (20747511837 / 1000000000000), orderedInterval (-29697416958 / 1000000000000) (-29697415016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3328003608413387 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7220729054 / 1000000000000) (-7220729053 / 1000000000000), orderedInterval (-26698251461 / 1000000000000) (-26698251460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2451392395246433 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27509521084 / 1000000000000) (-27509521083 / 1000000000000), orderedInterval (-16770856549 / 1000000000000) (-16770856548 / 1000000000000)))) (orderedInterval (-442134686 / 1000000000000) (-442134662 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks0_1 :
    compactCertificate549.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3761066338154159 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25747949601 / 1000000000000) (-25747922504 / 1000000000000), orderedInterval (3769572471 / 1000000000000) (3769599568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2171452662773111 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5212422466 / 1000000000000) (-5212422465 / 1000000000000), orderedInterval (-33841007581 / 1000000000000) (-33841007580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3853280855444899 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9139230579 / 1000000000000) (9139230582 / 1000000000000), orderedInterval (-24032529730 / 1000000000000) (-24032529727 / 1000000000000)))) (orderedInterval (5488092729 / 1000000000000) (5488097711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3600234809602831 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18950541114 / 1000000000000) (18950542537 / 1000000000000), orderedInterval (-18670274359 / 1000000000000) (-18670272936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2569297439637823 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24988487277 / 1000000000000) (24988507570 / 1000000000000), orderedInterval (-19168710718 / 1000000000000) (-19168690425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2913309458330217 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7688971103 / 1000000000000) (7688971104 / 1000000000000), orderedInterval (28542305543 / 1000000000000) (28542305544 / 1000000000000)))) (orderedInterval (1981956552 / 1000000000000) (1981958547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2428813698576473 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32247377465 / 1000000000000) (-32247374596 / 1000000000000), orderedInterval (2950934389 / 1000000000000) (2950937258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2145930561221933 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1909557261 / 1000000000000) (-1909557260 / 1000000000000), orderedInterval (-34393118727 / 1000000000000) (-34393118726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (621974318303367 / 800000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21720287370 / 1000000000000) (-21720281397 / 1000000000000), orderedInterval (18643688925 / 1000000000000) (18643694897 / 1000000000000)))) (orderedInterval (-819229629 / 1000000000000) (-819229402 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks0_2 :
    compactCertificate549.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1720413697142149 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18117764056 / 1000000000000) (-18117764055 / 1000000000000), orderedInterval (-33918623716 / 1000000000000) (-33918623715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1458413744127389 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34320108779 / 1000000000000) (34320108780 / 1000000000000), orderedInterval (23789679310 / 1000000000000) (23789679311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (912607604753567 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20546720592 / 1000000000000) (20546721349 / 1000000000000), orderedInterval (-48708874683 / 1000000000000) (-48708873926 / 1000000000000)))) (orderedInterval (1623280896 / 1000000000000) (1623281026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (490803405032289 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59135000313 / 1000000000000) (-59135000312 / 1000000000000), orderedInterval (-40885981018 / 1000000000000) (-40885981017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1332626719523867 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35116770761 / 1000000000000) (35116770762 / 1000000000000), orderedInterval (25979657455 / 1000000000000) (25979657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1819587855747259 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5633053555 / 1000000000000) (-5633053554 / 1000000000000), orderedInterval (-36976923046 / 1000000000000) (-36976923045 / 1000000000000)))) (orderedInterval (726956201 / 1000000000000) (726956252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (769392395246433 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57367969449 / 1000000000000) (-57367969428 / 1000000000000), orderedInterval (-4167404741 / 1000000000000) (-4167404720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3127537371288193 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11452806613 / 1000000000000) (-11452806612 / 1000000000000), orderedInterval (-26127816012 / 1000000000000) (-26127816011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2089050021229487 / 4000000000000) 0 (IntervalRat.scale (841 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900459535 / 1000000000000) (34900459965 / 1000000000000), orderedInterval (927035547 / 1000000000000) (927035977 / 1000000000000)))) (orderedInterval (-5961806279 / 1000000000000) (-5961806081 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks0 :
    compactCertificate549.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate549.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate549_chunkChecks0_0
    compactCertificate549_chunkChecks0_1 compactCertificate549_chunkChecks0_2

theorem compactCertificate549_chunkChecks1_0 :
    compactCertificate549.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (841 / 2) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932145852 / 1000000000000) (11932145853 / 1000000000000), orderedInterval (37020711663 / 1000000000000) (37020711664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1238953587184741 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21507310278 / 1000000000000) (21507311707 / 1000000000000), orderedInterval (-39944413212 / 1000000000000) (-39944411783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (400652134187653 / 800000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31006317309 / 1000000000000) (-31006217341 / 1000000000000), orderedInterval (17631418629 / 1000000000000) (17631518596 / 1000000000000)))) (orderedInterval (15631795588 / 1000000000000) (15631802618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (361523566746287 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4925320403 / 1000000000000) (-4925320400 / 1000000000000), orderedInterval (-83755754118 / 1000000000000) (-83755754115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (971103152776739 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51013146958 / 1000000000000) (-51013146653 / 1000000000000), orderedInterval (4566825581 / 1000000000000) (4566825886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2636733966255063 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7213138653 / 1000000000000) (7213138654 / 1000000000000), orderedInterval (30222679166 / 1000000000000) (30222679167 / 1000000000000)))) (orderedInterval (-3076478404 / 1000000000000) (-3076478340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1942206305554319 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20747509895 / 1000000000000) (20747511837 / 1000000000000), orderedInterval (-29697416958 / 1000000000000) (-29697415016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3328003608413387 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7220729054 / 1000000000000) (-7220729053 / 1000000000000), orderedInterval (-26698251461 / 1000000000000) (-26698251460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2451392395246433 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27509521084 / 1000000000000) (-27509521083 / 1000000000000), orderedInterval (-16770856549 / 1000000000000) (-16770856548 / 1000000000000)))) (orderedInterval (1038616309 / 1000000000000) (1038616351 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks1_1 :
    compactCertificate549.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3761066338154159 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25747949601 / 1000000000000) (-25747922504 / 1000000000000), orderedInterval (3769572471 / 1000000000000) (3769599568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2171452662773111 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5212422466 / 1000000000000) (-5212422465 / 1000000000000), orderedInterval (-33841007581 / 1000000000000) (-33841007580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3853280855444899 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9139230579 / 1000000000000) (9139230582 / 1000000000000), orderedInterval (-24032529730 / 1000000000000) (-24032529727 / 1000000000000)))) (orderedInterval (-12561234223 / 1000000000000) (-12561223111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3600234809602831 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18950541114 / 1000000000000) (18950542537 / 1000000000000), orderedInterval (-18670274359 / 1000000000000) (-18670272936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2569297439637823 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24988487277 / 1000000000000) (24988507570 / 1000000000000), orderedInterval (-19168710718 / 1000000000000) (-19168690425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2913309458330217 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7688971103 / 1000000000000) (7688971104 / 1000000000000), orderedInterval (28542305543 / 1000000000000) (28542305544 / 1000000000000)))) (orderedInterval (-2297593045 / 1000000000000) (-2297589977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2428813698576473 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32247377465 / 1000000000000) (-32247374596 / 1000000000000), orderedInterval (2950934389 / 1000000000000) (2950937258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2145930561221933 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1909557261 / 1000000000000) (-1909557260 / 1000000000000), orderedInterval (-34393118727 / 1000000000000) (-34393118726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (621974318303367 / 800000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21720287370 / 1000000000000) (-21720281397 / 1000000000000), orderedInterval (18643688925 / 1000000000000) (18643694897 / 1000000000000)))) (orderedInterval (3442864316 / 1000000000000) (3442864705 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks1_2 :
    compactCertificate549.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1720413697142149 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18117764056 / 1000000000000) (-18117764055 / 1000000000000), orderedInterval (-33918623716 / 1000000000000) (-33918623715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1458413744127389 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34320108779 / 1000000000000) (34320108780 / 1000000000000), orderedInterval (23789679310 / 1000000000000) (23789679311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (912607604753567 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20546720592 / 1000000000000) (20546721349 / 1000000000000), orderedInterval (-48708874683 / 1000000000000) (-48708873926 / 1000000000000)))) (orderedInterval (3519308858 / 1000000000000) (3519308969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (490803405032289 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59135000313 / 1000000000000) (-59135000312 / 1000000000000), orderedInterval (-40885981018 / 1000000000000) (-40885981017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1332626719523867 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35116770761 / 1000000000000) (35116770762 / 1000000000000), orderedInterval (25979657455 / 1000000000000) (25979657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1819587855747259 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5633053555 / 1000000000000) (-5633053554 / 1000000000000), orderedInterval (-36976923046 / 1000000000000) (-36976923045 / 1000000000000)))) (orderedInterval (2819005776 / 1000000000000) (2819005822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (769392395246433 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57367969449 / 1000000000000) (-57367969428 / 1000000000000), orderedInterval (-4167404741 / 1000000000000) (-4167404720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3127537371288193 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11452806613 / 1000000000000) (-11452806612 / 1000000000000), orderedInterval (-26127816012 / 1000000000000) (-26127816011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2089050021229487 / 4000000000000) 1 (IntervalRat.scale (841 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900459535 / 1000000000000) (34900459965 / 1000000000000), orderedInterval (927035547 / 1000000000000) (927035977 / 1000000000000)))) (orderedInterval (3727178109 / 1000000000000) (3727178373 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks1 :
    compactCertificate549.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate549.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate549_chunkChecks1_0
    compactCertificate549_chunkChecks1_1 compactCertificate549_chunkChecks1_2

theorem compactCertificate549_chunkChecks2_0 :
    compactCertificate549.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (841 / 2) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932145852 / 1000000000000) (11932145853 / 1000000000000), orderedInterval (37020711663 / 1000000000000) (37020711664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1238953587184741 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21507310278 / 1000000000000) (21507311707 / 1000000000000), orderedInterval (-39944413212 / 1000000000000) (-39944411783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (400652134187653 / 800000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31006317309 / 1000000000000) (-31006217341 / 1000000000000), orderedInterval (17631418629 / 1000000000000) (17631518596 / 1000000000000)))) (orderedInterval (-2294499699 / 1000000000000) (-2294491315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (361523566746287 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4925320403 / 1000000000000) (-4925320400 / 1000000000000), orderedInterval (-83755754118 / 1000000000000) (-83755754115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (971103152776739 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51013146958 / 1000000000000) (-51013146653 / 1000000000000), orderedInterval (4566825581 / 1000000000000) (4566825886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2636733966255063 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7213138653 / 1000000000000) (7213138654 / 1000000000000), orderedInterval (30222679166 / 1000000000000) (30222679167 / 1000000000000)))) (orderedInterval (1885825337 / 1000000000000) (1885825420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1942206305554319 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20747509895 / 1000000000000) (20747511837 / 1000000000000), orderedInterval (-29697416958 / 1000000000000) (-29697415016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3328003608413387 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7220729054 / 1000000000000) (-7220729053 / 1000000000000), orderedInterval (-26698251461 / 1000000000000) (-26698251460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2451392395246433 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27509521084 / 1000000000000) (-27509521083 / 1000000000000), orderedInterval (-16770856549 / 1000000000000) (-16770856548 / 1000000000000)))) (orderedInterval (537834202 / 1000000000000) (537834276 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks2_1 :
    compactCertificate549.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3761066338154159 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25747949601 / 1000000000000) (-25747922504 / 1000000000000), orderedInterval (3769572471 / 1000000000000) (3769599568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2171452662773111 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5212422466 / 1000000000000) (-5212422465 / 1000000000000), orderedInterval (-33841007581 / 1000000000000) (-33841007580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3853280855444899 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9139230579 / 1000000000000) (9139230582 / 1000000000000), orderedInterval (-24032529730 / 1000000000000) (-24032529727 / 1000000000000)))) (orderedInterval (-29020385907 / 1000000000000) (-29020361065 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3600234809602831 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18950541114 / 1000000000000) (18950542537 / 1000000000000), orderedInterval (-18670274359 / 1000000000000) (-18670272936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2569297439637823 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24988487277 / 1000000000000) (24988507570 / 1000000000000), orderedInterval (-19168710718 / 1000000000000) (-19168690425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2913309458330217 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7688971103 / 1000000000000) (7688971104 / 1000000000000), orderedInterval (28542305543 / 1000000000000) (28542305544 / 1000000000000)))) (orderedInterval (-3824025223 / 1000000000000) (-3824020485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2428813698576473 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32247377465 / 1000000000000) (-32247374596 / 1000000000000), orderedInterval (2950934389 / 1000000000000) (2950937258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2145930561221933 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1909557261 / 1000000000000) (-1909557260 / 1000000000000), orderedInterval (-34393118727 / 1000000000000) (-34393118726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (621974318303367 / 800000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21720287370 / 1000000000000) (-21720281397 / 1000000000000), orderedInterval (18643688925 / 1000000000000) (18643694897 / 1000000000000)))) (orderedInterval (2491511726 / 1000000000000) (2491512406 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks2_2 :
    compactCertificate549.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1720413697142149 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18117764056 / 1000000000000) (-18117764055 / 1000000000000), orderedInterval (-33918623716 / 1000000000000) (-33918623715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1458413744127389 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34320108779 / 1000000000000) (34320108780 / 1000000000000), orderedInterval (23789679310 / 1000000000000) (23789679311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (912607604753567 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20546720592 / 1000000000000) (20546721349 / 1000000000000), orderedInterval (-48708874683 / 1000000000000) (-48708873926 / 1000000000000)))) (orderedInterval (-1775600377 / 1000000000000) (-1775600276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (490803405032289 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59135000313 / 1000000000000) (-59135000312 / 1000000000000), orderedInterval (-40885981018 / 1000000000000) (-40885981017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1332626719523867 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35116770761 / 1000000000000) (35116770762 / 1000000000000), orderedInterval (25979657455 / 1000000000000) (25979657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1819587855747259 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5633053555 / 1000000000000) (-5633053554 / 1000000000000), orderedInterval (-36976923046 / 1000000000000) (-36976923045 / 1000000000000)))) (orderedInterval (-104808402 / 1000000000000) (-104808357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (769392395246433 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57367969449 / 1000000000000) (-57367969428 / 1000000000000), orderedInterval (-4167404741 / 1000000000000) (-4167404720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3127537371288193 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11452806613 / 1000000000000) (-11452806612 / 1000000000000), orderedInterval (-26127816012 / 1000000000000) (-26127816011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2089050021229487 / 4000000000000) 2 (IntervalRat.scale (841 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900459535 / 1000000000000) (34900459965 / 1000000000000), orderedInterval (927035547 / 1000000000000) (927035977 / 1000000000000)))) (orderedInterval (6941368146 / 1000000000000) (6941368513 / 1000000000000))) = true
  rfl'

theorem compactCertificate549_chunkChecks2 :
    compactCertificate549.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate549.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate549_chunkChecks2_0
    compactCertificate549_chunkChecks2_1 compactCertificate549_chunkChecks2_2

theorem compactCertificate549_chunkChecks3_0 :
    compactCertificate549.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (841 / 2) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932145852 / 1000000000000) (11932145853 / 1000000000000), orderedInterval (37020711663 / 1000000000000) (37020711664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1238953587184741 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21507310278 / 1000000000000) (21507311707 / 1000000000000), orderedInterval (-39944413212 / 1000000000000) (-39944411783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (400652134187653 / 800000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31006317309 / 1000000000000) (-31006217341 / 1000000000000), orderedInterval (17631418629 / 1000000000000) (17631518596 / 1000000000000)))) (orderedInterval (-16267339701 / 1000000000000) (-16267329721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (361523566746287 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4925320403 / 1000000000000) (-4925320400 / 1000000000000), orderedInterval (-83755754118 / 1000000000000) (-83755754115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (971103152776739 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51013146958 / 1000000000000) (-51013146653 / 1000000000000), orderedInterval (4566825581 / 1000000000000) (4566825886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2636733966255063 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7213138653 / 1000000000000) (7213138654 / 1000000000000), orderedInterval (30222679166 / 1000000000000) (30222679167 / 1000000000000)))) (orderedInterval (8231143060 / 1000000000000) (8231143181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1942206305554319 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20747509895 / 1000000000000) (20747511837 / 1000000000000), orderedInterval (-29697416958 / 1000000000000) (-29697415016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3328003608413387 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7220729054 / 1000000000000) (-7220729053 / 1000000000000), orderedInterval (-26698251461 / 1000000000000) (-26698251460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2451392395246433 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27509521084 / 1000000000000) (-27509521083 / 1000000000000), orderedInterval (-16770856549 / 1000000000000) (-16770856548 / 1000000000000)))) (orderedInterval (-5125146673 / 1000000000000) (-5125146540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate549_chunkChecks3_1 :
    compactCertificate549.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3761066338154159 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25747949601 / 1000000000000) (-25747922504 / 1000000000000), orderedInterval (3769572471 / 1000000000000) (3769599568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2171452662773111 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5212422466 / 1000000000000) (-5212422465 / 1000000000000), orderedInterval (-33841007581 / 1000000000000) (-33841007580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3853280855444899 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9139230579 / 1000000000000) (9139230582 / 1000000000000), orderedInterval (-24032529730 / 1000000000000) (-24032529727 / 1000000000000)))) (orderedInterval (54027630586 / 1000000000000) (54027686102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3600234809602831 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18950541114 / 1000000000000) (18950542537 / 1000000000000), orderedInterval (-18670274359 / 1000000000000) (-18670272936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2569297439637823 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24988487277 / 1000000000000) (24988507570 / 1000000000000), orderedInterval (-19168710718 / 1000000000000) (-19168690425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2913309458330217 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7688971103 / 1000000000000) (7688971104 / 1000000000000), orderedInterval (28542305543 / 1000000000000) (28542305544 / 1000000000000)))) (orderedInterval (3914952080 / 1000000000000) (3914959411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2428813698576473 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32247377465 / 1000000000000) (-32247374596 / 1000000000000), orderedInterval (2950934389 / 1000000000000) (2950937258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2145930561221933 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1909557261 / 1000000000000) (-1909557260 / 1000000000000), orderedInterval (-34393118727 / 1000000000000) (-34393118726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (621974318303367 / 800000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21720287370 / 1000000000000) (-21720281397 / 1000000000000), orderedInterval (18643688925 / 1000000000000) (18643694897 / 1000000000000)))) (orderedInterval (-7212923472 / 1000000000000) (-7212922271 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate549_chunkChecks3_2 :
    compactCertificate549.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1720413697142149 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18117764056 / 1000000000000) (-18117764055 / 1000000000000), orderedInterval (-33918623716 / 1000000000000) (-33918623715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1458413744127389 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34320108779 / 1000000000000) (34320108780 / 1000000000000), orderedInterval (23789679310 / 1000000000000) (23789679311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (912607604753567 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20546720592 / 1000000000000) (20546721349 / 1000000000000), orderedInterval (-48708874683 / 1000000000000) (-48708873926 / 1000000000000)))) (orderedInterval (-4668187897 / 1000000000000) (-4668187802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (490803405032289 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59135000313 / 1000000000000) (-59135000312 / 1000000000000), orderedInterval (-40885981018 / 1000000000000) (-40885981017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1332626719523867 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35116770761 / 1000000000000) (35116770762 / 1000000000000), orderedInterval (25979657455 / 1000000000000) (25979657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1819587855747259 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5633053555 / 1000000000000) (-5633053554 / 1000000000000), orderedInterval (-36976923046 / 1000000000000) (-36976923045 / 1000000000000)))) (orderedInterval (-3313105556 / 1000000000000) (-3313105509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (769392395246433 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57367969449 / 1000000000000) (-57367969428 / 1000000000000), orderedInterval (-4167404741 / 1000000000000) (-4167404720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3127537371288193 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11452806613 / 1000000000000) (-11452806612 / 1000000000000), orderedInterval (-26127816012 / 1000000000000) (-26127816011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2089050021229487 / 4000000000000) 3 (IntervalRat.scale (841 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900459535 / 1000000000000) (34900459965 / 1000000000000), orderedInterval (927035547 / 1000000000000) (927035977 / 1000000000000)))) (orderedInterval (-13353926388 / 1000000000000) (-13353925861 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate549_chunkChecks3 :
    compactCertificate549.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate549.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate549_chunkChecks3_0
    compactCertificate549_chunkChecks3_1 compactCertificate549_chunkChecks3_2

theorem compactCertificate549_chunkChecks4_0 :
    compactCertificate549.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (841 / 2) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932145852 / 1000000000000) (11932145853 / 1000000000000), orderedInterval (37020711663 / 1000000000000) (37020711664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1238953587184741 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21507310278 / 1000000000000) (21507311707 / 1000000000000), orderedInterval (-39944413212 / 1000000000000) (-39944411783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (400652134187653 / 800000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31006317309 / 1000000000000) (-31006217341 / 1000000000000), orderedInterval (17631418629 / 1000000000000) (17631518596 / 1000000000000)))) (orderedInterval (1204882812 / 1000000000000) (1204894719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (361523566746287 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4925320403 / 1000000000000) (-4925320400 / 1000000000000), orderedInterval (-83755754118 / 1000000000000) (-83755754115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (971103152776739 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51013146958 / 1000000000000) (-51013146653 / 1000000000000), orderedInterval (4566825581 / 1000000000000) (4566825886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2636733966255063 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7213138653 / 1000000000000) (7213138654 / 1000000000000), orderedInterval (30222679166 / 1000000000000) (30222679167 / 1000000000000)))) (orderedInterval (-3342626235 / 1000000000000) (-3342626050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1942206305554319 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20747509895 / 1000000000000) (20747511837 / 1000000000000), orderedInterval (-29697416958 / 1000000000000) (-29697415016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3328003608413387 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7220729054 / 1000000000000) (-7220729053 / 1000000000000), orderedInterval (-26698251461 / 1000000000000) (-26698251460 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2451392395246433 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27509521084 / 1000000000000) (-27509521083 / 1000000000000), orderedInterval (-16770856549 / 1000000000000) (-16770856548 / 1000000000000)))) (orderedInterval (438089021 / 1000000000000) (438089267 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate549_chunkChecks4_1 :
    compactCertificate549.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3761066338154159 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25747949601 / 1000000000000) (-25747922504 / 1000000000000), orderedInterval (3769572471 / 1000000000000) (3769599568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2171452662773111 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5212422466 / 1000000000000) (-5212422465 / 1000000000000), orderedInterval (-33841007581 / 1000000000000) (-33841007580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3853280855444899 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9139230579 / 1000000000000) (9139230582 / 1000000000000), orderedInterval (-24032529730 / 1000000000000) (-24032529727 / 1000000000000)))) (orderedInterval (148831822942 / 1000000000000) (148831947182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3600234809602831 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18950541114 / 1000000000000) (18950542537 / 1000000000000), orderedInterval (-18670274359 / 1000000000000) (-18670272936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2569297439637823 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24988487277 / 1000000000000) (24988507570 / 1000000000000), orderedInterval (-19168710718 / 1000000000000) (-19168690425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2913309458330217 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7688971103 / 1000000000000) (7688971104 / 1000000000000), orderedInterval (28542305543 / 1000000000000) (28542305544 / 1000000000000)))) (orderedInterval (5315167404 / 1000000000000) (5315178820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2428813698576473 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32247377465 / 1000000000000) (-32247374596 / 1000000000000), orderedInterval (2950934389 / 1000000000000) (2950937258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2145930561221933 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1909557261 / 1000000000000) (-1909557260 / 1000000000000), orderedInterval (-34393118727 / 1000000000000) (-34393118726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (621974318303367 / 800000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21720287370 / 1000000000000) (-21720281397 / 1000000000000), orderedInterval (18643688925 / 1000000000000) (18643694897 / 1000000000000)))) (orderedInterval (-7794085375 / 1000000000000) (-7794083227 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate549_chunkChecks4_2 :
    compactCertificate549.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1720413697142149 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18117764056 / 1000000000000) (-18117764055 / 1000000000000), orderedInterval (-33918623716 / 1000000000000) (-33918623715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1458413744127389 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34320108779 / 1000000000000) (34320108780 / 1000000000000), orderedInterval (23789679310 / 1000000000000) (23789679311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (912607604753567 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20546720592 / 1000000000000) (20546721349 / 1000000000000), orderedInterval (-48708874683 / 1000000000000) (-48708873926 / 1000000000000)))) (orderedInterval (2152945261 / 1000000000000) (2152945352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (490803405032289 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59135000313 / 1000000000000) (-59135000312 / 1000000000000), orderedInterval (-40885981018 / 1000000000000) (-40885981017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1332626719523867 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35116770761 / 1000000000000) (35116770762 / 1000000000000), orderedInterval (25979657455 / 1000000000000) (25979657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1819587855747259 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5633053555 / 1000000000000) (-5633053554 / 1000000000000), orderedInterval (-36976923046 / 1000000000000) (-36976923045 / 1000000000000)))) (orderedInterval (301017082 / 1000000000000) (301017132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (769392395246433 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57367969449 / 1000000000000) (-57367969428 / 1000000000000), orderedInterval (-4167404741 / 1000000000000) (-4167404720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3127537371288193 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11452806613 / 1000000000000) (-11452806612 / 1000000000000), orderedInterval (-26127816012 / 1000000000000) (-26127816011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2089050021229487 / 4000000000000) 4 (IntervalRat.scale (841 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900459535 / 1000000000000) (34900459965 / 1000000000000), orderedInterval (927035547 / 1000000000000) (927035977 / 1000000000000)))) (orderedInterval (-4389080757 / 1000000000000) (-4389079965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate549_chunkChecks4 :
    compactCertificate549.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate549.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate549_chunkChecks4_0
    compactCertificate549_chunkChecks4_1 compactCertificate549_chunkChecks4_2

theorem compactCertificate549_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate549.chunkCheck r b = true :=
  compactCertificate549.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate549_chunkChecks0
    · exact compactCertificate549_chunkChecks1
    · exact compactCertificate549_chunkChecks2
    · exact compactCertificate549_chunkChecks3
    · exact compactCertificate549_chunkChecks4)

theorem compactCertificate549_coefficient0 :
    compactCertificate549.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate549_coefficient1 :
    compactCertificate549.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate549_coefficient2 :
    compactCertificate549.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate549_coefficient3 :
    compactCertificate549.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate549_coefficient4 :
    compactCertificate549.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate549_coefficients : ∀ r : Fin 5,
    compactCertificate549.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate549_coefficient0
  · exact compactCertificate549_coefficient1
  · exact compactCertificate549_coefficient2
  · exact compactCertificate549_coefficient3
  · exact compactCertificate549_coefficient4

theorem compactCertificate549_lower : (1 : ℚ) ≤ compactCertificate549.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate549, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate549_proves {t : ℝ} (ht : t ∈ compactCertificate549.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate549.proves compactCertificate549_states compactCertificate549_chunks
    compactCertificate549_coefficients compactCertificate549_lower ht

end Erdos232
