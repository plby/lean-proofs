/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate485 : CompactCertificate where
  left := 356
  right := 357
  center := 713 / 2
  grid := fun i =>
    match i.val with
    | 0 => 114
    | 1 => 84
    | 2 => 135
    | 3 => 24
    | 4 => 66
    | 5 => 178
    | 6 => 131
    | 7 => 225
    | 8 => 165
    | 9 => 254
    | 10 => 147
    | 11 => 260
    | 12 => 243
    | 13 => 173
    | 14 => 197
    | 15 => 164
    | 16 => 145
    | 17 => 210
    | 18 => 116
    | 19 => 98
    | 20 => 62
    | 21 => 33
    | 22 => 90
    | 23 => 123
    | 24 => 52
    | 25 => 211
    | _ => 141
  point := fun i =>
    match i.val with
    | 0 => 713 / 2
    | 1 => 1050385145853413 / 4000000000000
    | 2 => 339672974644229 / 800000000000
    | 3 => 306499765862191 / 4000000000000
    | 4 => 823301483864227 / 4000000000000
    | 5 => 2235423683638359 / 4000000000000
    | 6 => 1646602967729167 / 4000000000000
    | 7 => 2821482250652491 / 4000000000000
    | 8 => 2078291055660769 / 4000000000000
    | 9 => 3188632935914287 / 4000000000000
    | 10 => 1840958083896823 / 4000000000000
    | 11 => 3266812425603107 / 4000000000000
    | 12 => 3052279927760783 / 4000000000000
    | 13 => 2178250980335039 / 4000000000000
    | 14 => 2469904451592681 / 4000000000000
    | 15 => 2059148831254489 / 4000000000000
    | 16 => 1819320440132269 / 4000000000000
    | 17 => 527309974970631 / 800000000000
    | 18 => 1458567141572357 / 4000000000000
    | 19 => 1236443519099677 / 4000000000000
    | 20 => 773708944339231 / 4000000000000
    | 21 => 416103243505377 / 4000000000000
    | 22 => 1129801249727131 / 4000000000000
    | 23 => 1542647016822587 / 4000000000000
    | 24 => 652291055660769 / 4000000000000
    | 25 => 2651526927144449 / 4000000000000
    | _ => 1771097104799791 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-31928737321 / 1000000000000) (-31928693332 / 1000000000000), orderedInterval (27727000762 / 1000000000000) (27727044751 / 1000000000000))
    | 1 => (orderedInterval (-24147135921 / 1000000000000) (-24147133614 / 1000000000000), orderedInterval (42955731441 / 1000000000000) (42955733747 / 1000000000000))
    | 2 => (orderedInterval (-36882082111 / 1000000000000) (-36882082108 / 1000000000000), orderedInterval (-11749879377 / 1000000000000) (-11749879374 / 1000000000000))
    | 3 => (orderedInterval (82479004121 / 1000000000000) (82479010940 / 1000000000000), orderedInterval (-39337128136 / 1000000000000) (-39337121316 / 1000000000000))
    | 4 => (orderedInterval (-37292622783 / 1000000000000) (-37292593601 / 1000000000000), orderedInterval (41349169993 / 1000000000000) (41349199175 / 1000000000000))
    | 5 => (orderedInterval (14302760156 / 1000000000000) (14302760157 / 1000000000000), orderedInterval (30558098924 / 1000000000000) (30558098925 / 1000000000000))
    | 6 => (orderedInterval (-30489364613 / 1000000000000) (-30489364612 / 1000000000000), orderedInterval (-24800499700 / 1000000000000) (-24800499699 / 1000000000000))
    | 7 => (orderedInterval (19412536252 / 1000000000000) (19412537816 / 1000000000000), orderedInterval (-22941600744 / 1000000000000) (-22941599180 / 1000000000000))
    | 8 => (orderedInterval (-31899514700 / 1000000000000) (-31899465440 / 1000000000000), orderedInterval (14442390206 / 1000000000000) (14442439466 / 1000000000000))
    | 9 => (orderedInterval (-595068181 / 1000000000000) (-595068180 / 1000000000000), orderedInterval (28253826133 / 1000000000000) (28253826134 / 1000000000000))
    | 10 => (orderedInterval (26405545628 / 1000000000000) (26405560121 / 1000000000000), orderedInterval (-26219962181 / 1000000000000) (-26219947688 / 1000000000000))
    | 11 => (orderedInterval (17430731766 / 1000000000000) (17430731767 / 1000000000000), orderedInterval (21799171704 / 1000000000000) (21799171705 / 1000000000000))
    | 12 => (orderedInterval (-12516761319 / 1000000000000) (-12516761318 / 1000000000000), orderedInterval (-26022901558 / 1000000000000) (-26022901557 / 1000000000000))
    | 13 => (orderedInterval (-32844722431 / 1000000000000) (-32844707616 / 1000000000000), orderedInterval (9531300302 / 1000000000000) (9531315117 / 1000000000000))
    | 14 => (orderedInterval (18980341538 / 1000000000000) (18980342700 / 1000000000000), orderedInterval (-25914207498 / 1000000000000) (-25914206336 / 1000000000000))
    | 15 => (orderedInterval (12097005503 / 1000000000000) (12097005504 / 1000000000000), orderedInterval (33008377342 / 1000000000000) (33008377343 / 1000000000000))
    | 16 => (orderedInterval (-3150077165 / 1000000000000) (-3150077164 / 1000000000000), orderedInterval (-37276086495 / 1000000000000) (-37276086494 / 1000000000000))
    | 17 => (orderedInterval (5815009325 / 1000000000000) (5815009326 / 1000000000000), orderedInterval (30524649797 / 1000000000000) (30524649798 / 1000000000000))
    | 18 => (orderedInterval (35206923356 / 1000000000000) (35206923357 / 1000000000000), orderedInterval (22453924820 / 1000000000000) (22453924821 / 1000000000000))
    | 19 => (orderedInterval (40883758990 / 1000000000000) (40883782407 / 1000000000000), orderedInterval (-19764739312 / 1000000000000) (-19764715895 / 1000000000000))
    | 20 => (orderedInterval (-30801563614 / 1000000000000) (-30801557600 / 1000000000000), orderedInterval (48479315499 / 1000000000000) (48479321512 / 1000000000000))
    | 21 => (orderedInterval (-70997824687 / 1000000000000) (-70997824686 / 1000000000000), orderedInterval (-32508235909 / 1000000000000) (-32508235908 / 1000000000000))
    | 22 => (orderedInterval (22423926976 / 1000000000000) (22423926977 / 1000000000000), orderedInterval (41806298653 / 1000000000000) (41806298654 / 1000000000000))
    | 23 => (orderedInterval (-1256531495 / 1000000000000) (-1256531493 / 1000000000000), orderedInterval (-40608013095 / 1000000000000) (-40608013094 / 1000000000000))
    | 24 => (orderedInterval (29657248739 / 1000000000000) (29657248740 / 1000000000000), orderedInterval (54903229212 / 1000000000000) (54903229213 / 1000000000000))
    | 25 => (orderedInterval (-22033304294 / 1000000000000) (-22033304293 / 1000000000000), orderedInterval (-21775939803 / 1000000000000) (-21775939802 / 1000000000000))
    | _ => (orderedInterval (-21248128246 / 1000000000000) (-21248128245 / 1000000000000), orderedInterval (-31381657177 / 1000000000000) (-31381657176 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15044720843 / 1000000000000) (-15044703360 / 1000000000000)
      | 1 => orderedInterval (-3273235668 / 1000000000000) (-3273234486 / 1000000000000)
      | 2 => orderedInterval (-1369708679 / 1000000000000) (-1369707419 / 1000000000000)
      | 3 => orderedInterval (4540051222 / 1000000000000) (4540052438 / 1000000000000)
      | 4 => orderedInterval (-2975976406 / 1000000000000) (-2975974956 / 1000000000000)
      | 5 => orderedInterval (468847867 / 1000000000000) (468847901 / 1000000000000)
      | 6 => orderedInterval (-8946094532 / 1000000000000) (-8946092921 / 1000000000000)
      | 7 => orderedInterval (898553735 / 1000000000000) (898553778 / 1000000000000)
      | _ => orderedInterval (5959046204 / 1000000000000) (5959046303 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (10463655592 / 1000000000000) (10463673072 / 1000000000000)
      | 1 => orderedInterval (-2442064093 / 1000000000000) (-2442063413 / 1000000000000)
      | 2 => orderedInterval (1908784159 / 1000000000000) (1908786024 / 1000000000000)
      | 3 => orderedInterval (-6634666387 / 1000000000000) (-6634664707 / 1000000000000)
      | 4 => orderedInterval (2609481106 / 1000000000000) (2609483326 / 1000000000000)
      | 5 => orderedInterval (4716995175 / 1000000000000) (4716995225 / 1000000000000)
      | 6 => orderedInterval (-1845910001 / 1000000000000) (-1845908662 / 1000000000000)
      | 7 => orderedInterval (2790436008 / 1000000000000) (2790436047 / 1000000000000)
      | _ => orderedInterval (10760353536 / 1000000000000) (10760353676 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15818136193 / 1000000000000) (15818153722 / 1000000000000)
      | 1 => orderedInterval (3000720246 / 1000000000000) (3000720674 / 1000000000000)
      | 2 => orderedInterval (3976268991 / 1000000000000) (3976271776 / 1000000000000)
      | 3 => orderedInterval (-16775181810 / 1000000000000) (-16775179387 / 1000000000000)
      | 4 => orderedInterval (6492641809 / 1000000000000) (6492645216 / 1000000000000)
      | 5 => orderedInterval (-1106904231 / 1000000000000) (-1106904157 / 1000000000000)
      | 6 => orderedInterval (7929465057 / 1000000000000) (7929466194 / 1000000000000)
      | 7 => orderedInterval (87188299 / 1000000000000) (87188338 / 1000000000000)
      | _ => orderedInterval (-12418455486 / 1000000000000) (-12418455281 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10029446275 / 1000000000000) (-10029428744 / 1000000000000)
      | 1 => orderedInterval (8065393473 / 1000000000000) (8065393781 / 1000000000000)
      | 2 => orderedInterval (-6572783397 / 1000000000000) (-6572779217 / 1000000000000)
      | 3 => orderedInterval (23098419243 / 1000000000000) (23098422938 / 1000000000000)
      | 4 => orderedInterval (-8519122846 / 1000000000000) (-8519117619 / 1000000000000)
      | 5 => orderedInterval (-10514258164 / 1000000000000) (-10514258050 / 1000000000000)
      | 6 => orderedInterval (2838267674 / 1000000000000) (2838268649 / 1000000000000)
      | 7 => orderedInterval (-3483490779 / 1000000000000) (-3483490739 / 1000000000000)
      | _ => orderedInterval (-22673209554 / 1000000000000) (-22673209238 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17019997762 / 1000000000000) (-17019980178 / 1000000000000)
      | 1 => orderedInterval (-6338694808 / 1000000000000) (-6338694532 / 1000000000000)
      | 2 => orderedInterval (-12618090765 / 1000000000000) (-12618084423 / 1000000000000)
      | 3 => orderedInterval (76197684294 / 1000000000000) (76197690352 / 1000000000000)
      | 4 => orderedInterval (-12983365464 / 1000000000000) (-12983357419 / 1000000000000)
      | 5 => orderedInterval (2883846923 / 1000000000000) (2883847103 / 1000000000000)
      | 6 => orderedInterval (-7572156668 / 1000000000000) (-7572155821 / 1000000000000)
      | 7 => orderedInterval (-39517358 / 1000000000000) (-39517316 / 1000000000000)
      | _ => orderedInterval (31061178010 / 1000000000000) (31061178518 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-19743237100 / 1000000000000) (-19743212722 / 1000000000000)
    | 1 => orderedInterval (22327065095 / 1000000000000) (22327090588 / 1000000000000)
    | 2 => orderedInterval (7003879068 / 1000000000000) (7003907095 / 1000000000000)
    | 3 => orderedInterval (-27790230625 / 1000000000000) (-27790198239 / 1000000000000)
    | _ => orderedInterval (53570886402 / 1000000000000) (53570926284 / 1000000000000)

theorem compactCertificate485_stateChecks0 :
    compactCertificate485.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (713 / 2)) (orderedInterval (-31928737321 / 1000000000000) (-31928693332 / 1000000000000), orderedInterval (27727000762 / 1000000000000) (27727044751 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1050385145853413 / 4000000000000)) (orderedInterval (-24147135921 / 1000000000000) (-24147133614 / 1000000000000), orderedInterval (42955731441 / 1000000000000) (42955733747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (339672974644229 / 800000000000)) (orderedInterval (-36882082111 / 1000000000000) (-36882082108 / 1000000000000), orderedInterval (-11749879377 / 1000000000000) (-11749879374 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_stateChecks1 :
    compactCertificate485.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (306499765862191 / 4000000000000)) (orderedInterval (82479004121 / 1000000000000) (82479010940 / 1000000000000), orderedInterval (-39337128136 / 1000000000000) (-39337121316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (823301483864227 / 4000000000000)) (orderedInterval (-37292622783 / 1000000000000) (-37292593601 / 1000000000000), orderedInterval (41349169993 / 1000000000000) (41349199175 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2235423683638359 / 4000000000000)) (orderedInterval (14302760156 / 1000000000000) (14302760157 / 1000000000000), orderedInterval (30558098924 / 1000000000000) (30558098925 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_stateChecks2 :
    compactCertificate485.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1646602967729167 / 4000000000000)) (orderedInterval (-30489364613 / 1000000000000) (-30489364612 / 1000000000000), orderedInterval (-24800499700 / 1000000000000) (-24800499699 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2821482250652491 / 4000000000000)) (orderedInterval (19412536252 / 1000000000000) (19412537816 / 1000000000000), orderedInterval (-22941600744 / 1000000000000) (-22941599180 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2078291055660769 / 4000000000000)) (orderedInterval (-31899514700 / 1000000000000) (-31899465440 / 1000000000000), orderedInterval (14442390206 / 1000000000000) (14442439466 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_stateChecks3 :
    compactCertificate485.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (3188632935914287 / 4000000000000)) (orderedInterval (-595068181 / 1000000000000) (-595068180 / 1000000000000), orderedInterval (28253826133 / 1000000000000) (28253826134 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1840958083896823 / 4000000000000)) (orderedInterval (26405545628 / 1000000000000) (26405560121 / 1000000000000), orderedInterval (-26219962181 / 1000000000000) (-26219947688 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (3266812425603107 / 4000000000000)) (orderedInterval (17430731766 / 1000000000000) (17430731767 / 1000000000000), orderedInterval (21799171704 / 1000000000000) (21799171705 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_stateChecks4 :
    compactCertificate485.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3052279927760783 / 4000000000000)) (orderedInterval (-12516761319 / 1000000000000) (-12516761318 / 1000000000000), orderedInterval (-26022901558 / 1000000000000) (-26022901557 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2178250980335039 / 4000000000000)) (orderedInterval (-32844722431 / 1000000000000) (-32844707616 / 1000000000000), orderedInterval (9531300302 / 1000000000000) (9531315117 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2469904451592681 / 4000000000000)) (orderedInterval (18980341538 / 1000000000000) (18980342700 / 1000000000000), orderedInterval (-25914207498 / 1000000000000) (-25914206336 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_stateChecks5 :
    compactCertificate485.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2059148831254489 / 4000000000000)) (orderedInterval (12097005503 / 1000000000000) (12097005504 / 1000000000000), orderedInterval (33008377342 / 1000000000000) (33008377343 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1819320440132269 / 4000000000000)) (orderedInterval (-3150077165 / 1000000000000) (-3150077164 / 1000000000000), orderedInterval (-37276086495 / 1000000000000) (-37276086494 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (527309974970631 / 800000000000)) (orderedInterval (5815009325 / 1000000000000) (5815009326 / 1000000000000), orderedInterval (30524649797 / 1000000000000) (30524649798 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_stateChecks6 :
    compactCertificate485.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1458567141572357 / 4000000000000)) (orderedInterval (35206923356 / 1000000000000) (35206923357 / 1000000000000), orderedInterval (22453924820 / 1000000000000) (22453924821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1236443519099677 / 4000000000000)) (orderedInterval (40883758990 / 1000000000000) (40883782407 / 1000000000000), orderedInterval (-19764739312 / 1000000000000) (-19764715895 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (773708944339231 / 4000000000000)) (orderedInterval (-30801563614 / 1000000000000) (-30801557600 / 1000000000000), orderedInterval (48479315499 / 1000000000000) (48479321512 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_stateChecks7 :
    compactCertificate485.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (416103243505377 / 4000000000000)) (orderedInterval (-70997824687 / 1000000000000) (-70997824686 / 1000000000000), orderedInterval (-32508235909 / 1000000000000) (-32508235908 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1129801249727131 / 4000000000000)) (orderedInterval (22423926976 / 1000000000000) (22423926977 / 1000000000000), orderedInterval (41806298653 / 1000000000000) (41806298654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1542647016822587 / 4000000000000)) (orderedInterval (-1256531495 / 1000000000000) (-1256531493 / 1000000000000), orderedInterval (-40608013095 / 1000000000000) (-40608013094 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_stateChecks8 :
    compactCertificate485.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (652291055660769 / 4000000000000)) (orderedInterval (29657248739 / 1000000000000) (29657248740 / 1000000000000), orderedInterval (54903229212 / 1000000000000) (54903229213 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2651526927144449 / 4000000000000)) (orderedInterval (-22033304294 / 1000000000000) (-22033304293 / 1000000000000), orderedInterval (-21775939803 / 1000000000000) (-21775939802 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1771097104799791 / 4000000000000)) (orderedInterval (-21248128246 / 1000000000000) (-21248128245 / 1000000000000), orderedInterval (-31381657177 / 1000000000000) (-31381657176 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_states : ∀ j,
    BesselStateValid (compactCertificate485.point j) (compactCertificate485.state j) :=
  compactCertificate485.statesValid_of_checks3 compactCertificate485_stateChecks0
    compactCertificate485_stateChecks1 compactCertificate485_stateChecks2
    compactCertificate485_stateChecks3 compactCertificate485_stateChecks4
    compactCertificate485_stateChecks5 compactCertificate485_stateChecks6
    compactCertificate485_stateChecks7 compactCertificate485_stateChecks8

theorem compactCertificate485_chunkChecks0_0 :
    compactCertificate485.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (713 / 2) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31928737321 / 1000000000000) (-31928693332 / 1000000000000), orderedInterval (27727000762 / 1000000000000) (27727044751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1050385145853413 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24147135921 / 1000000000000) (-24147133614 / 1000000000000), orderedInterval (42955731441 / 1000000000000) (42955733747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (339672974644229 / 800000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36882082111 / 1000000000000) (-36882082108 / 1000000000000), orderedInterval (-11749879377 / 1000000000000) (-11749879374 / 1000000000000)))) (orderedInterval (-15044720843 / 1000000000000) (-15044703360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (306499765862191 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82479004121 / 1000000000000) (82479010940 / 1000000000000), orderedInterval (-39337128136 / 1000000000000) (-39337121316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (823301483864227 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37292622783 / 1000000000000) (-37292593601 / 1000000000000), orderedInterval (41349169993 / 1000000000000) (41349199175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2235423683638359 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14302760156 / 1000000000000) (14302760157 / 1000000000000), orderedInterval (30558098924 / 1000000000000) (30558098925 / 1000000000000)))) (orderedInterval (-3273235668 / 1000000000000) (-3273234486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1646602967729167 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30489364613 / 1000000000000) (-30489364612 / 1000000000000), orderedInterval (-24800499700 / 1000000000000) (-24800499699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2821482250652491 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19412536252 / 1000000000000) (19412537816 / 1000000000000), orderedInterval (-22941600744 / 1000000000000) (-22941599180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2078291055660769 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31899514700 / 1000000000000) (-31899465440 / 1000000000000), orderedInterval (14442390206 / 1000000000000) (14442439466 / 1000000000000)))) (orderedInterval (-1369708679 / 1000000000000) (-1369707419 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks0_1 :
    compactCertificate485.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3188632935914287 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-595068181 / 1000000000000) (-595068180 / 1000000000000), orderedInterval (28253826133 / 1000000000000) (28253826134 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1840958083896823 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26405545628 / 1000000000000) (26405560121 / 1000000000000), orderedInterval (-26219962181 / 1000000000000) (-26219947688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3266812425603107 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17430731766 / 1000000000000) (17430731767 / 1000000000000), orderedInterval (21799171704 / 1000000000000) (21799171705 / 1000000000000)))) (orderedInterval (4540051222 / 1000000000000) (4540052438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3052279927760783 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12516761319 / 1000000000000) (-12516761318 / 1000000000000), orderedInterval (-26022901558 / 1000000000000) (-26022901557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2178250980335039 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32844722431 / 1000000000000) (-32844707616 / 1000000000000), orderedInterval (9531300302 / 1000000000000) (9531315117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2469904451592681 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18980341538 / 1000000000000) (18980342700 / 1000000000000), orderedInterval (-25914207498 / 1000000000000) (-25914206336 / 1000000000000)))) (orderedInterval (-2975976406 / 1000000000000) (-2975974956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2059148831254489 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12097005503 / 1000000000000) (12097005504 / 1000000000000), orderedInterval (33008377342 / 1000000000000) (33008377343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1819320440132269 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3150077165 / 1000000000000) (-3150077164 / 1000000000000), orderedInterval (-37276086495 / 1000000000000) (-37276086494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (527309974970631 / 800000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5815009325 / 1000000000000) (5815009326 / 1000000000000), orderedInterval (30524649797 / 1000000000000) (30524649798 / 1000000000000)))) (orderedInterval (468847867 / 1000000000000) (468847901 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks0_2 :
    compactCertificate485.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1458567141572357 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35206923356 / 1000000000000) (35206923357 / 1000000000000), orderedInterval (22453924820 / 1000000000000) (22453924821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1236443519099677 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40883758990 / 1000000000000) (40883782407 / 1000000000000), orderedInterval (-19764739312 / 1000000000000) (-19764715895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (773708944339231 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-30801563614 / 1000000000000) (-30801557600 / 1000000000000), orderedInterval (48479315499 / 1000000000000) (48479321512 / 1000000000000)))) (orderedInterval (-8946094532 / 1000000000000) (-8946092921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (416103243505377 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70997824687 / 1000000000000) (-70997824686 / 1000000000000), orderedInterval (-32508235909 / 1000000000000) (-32508235908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1129801249727131 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22423926976 / 1000000000000) (22423926977 / 1000000000000), orderedInterval (41806298653 / 1000000000000) (41806298654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1542647016822587 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1256531495 / 1000000000000) (-1256531493 / 1000000000000), orderedInterval (-40608013095 / 1000000000000) (-40608013094 / 1000000000000)))) (orderedInterval (898553735 / 1000000000000) (898553778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (652291055660769 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29657248739 / 1000000000000) (29657248740 / 1000000000000), orderedInterval (54903229212 / 1000000000000) (54903229213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2651526927144449 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22033304294 / 1000000000000) (-22033304293 / 1000000000000), orderedInterval (-21775939803 / 1000000000000) (-21775939802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1771097104799791 / 4000000000000) 0 (IntervalRat.scale (713 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21248128246 / 1000000000000) (-21248128245 / 1000000000000), orderedInterval (-31381657177 / 1000000000000) (-31381657176 / 1000000000000)))) (orderedInterval (5959046204 / 1000000000000) (5959046303 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks0 :
    compactCertificate485.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate485.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate485_chunkChecks0_0
    compactCertificate485_chunkChecks0_1 compactCertificate485_chunkChecks0_2

theorem compactCertificate485_chunkChecks1_0 :
    compactCertificate485.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (713 / 2) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31928737321 / 1000000000000) (-31928693332 / 1000000000000), orderedInterval (27727000762 / 1000000000000) (27727044751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1050385145853413 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24147135921 / 1000000000000) (-24147133614 / 1000000000000), orderedInterval (42955731441 / 1000000000000) (42955733747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (339672974644229 / 800000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36882082111 / 1000000000000) (-36882082108 / 1000000000000), orderedInterval (-11749879377 / 1000000000000) (-11749879374 / 1000000000000)))) (orderedInterval (10463655592 / 1000000000000) (10463673072 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (306499765862191 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82479004121 / 1000000000000) (82479010940 / 1000000000000), orderedInterval (-39337128136 / 1000000000000) (-39337121316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (823301483864227 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37292622783 / 1000000000000) (-37292593601 / 1000000000000), orderedInterval (41349169993 / 1000000000000) (41349199175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2235423683638359 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14302760156 / 1000000000000) (14302760157 / 1000000000000), orderedInterval (30558098924 / 1000000000000) (30558098925 / 1000000000000)))) (orderedInterval (-2442064093 / 1000000000000) (-2442063413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1646602967729167 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30489364613 / 1000000000000) (-30489364612 / 1000000000000), orderedInterval (-24800499700 / 1000000000000) (-24800499699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2821482250652491 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19412536252 / 1000000000000) (19412537816 / 1000000000000), orderedInterval (-22941600744 / 1000000000000) (-22941599180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2078291055660769 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31899514700 / 1000000000000) (-31899465440 / 1000000000000), orderedInterval (14442390206 / 1000000000000) (14442439466 / 1000000000000)))) (orderedInterval (1908784159 / 1000000000000) (1908786024 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks1_1 :
    compactCertificate485.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3188632935914287 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-595068181 / 1000000000000) (-595068180 / 1000000000000), orderedInterval (28253826133 / 1000000000000) (28253826134 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1840958083896823 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26405545628 / 1000000000000) (26405560121 / 1000000000000), orderedInterval (-26219962181 / 1000000000000) (-26219947688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3266812425603107 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17430731766 / 1000000000000) (17430731767 / 1000000000000), orderedInterval (21799171704 / 1000000000000) (21799171705 / 1000000000000)))) (orderedInterval (-6634666387 / 1000000000000) (-6634664707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3052279927760783 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12516761319 / 1000000000000) (-12516761318 / 1000000000000), orderedInterval (-26022901558 / 1000000000000) (-26022901557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2178250980335039 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32844722431 / 1000000000000) (-32844707616 / 1000000000000), orderedInterval (9531300302 / 1000000000000) (9531315117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2469904451592681 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18980341538 / 1000000000000) (18980342700 / 1000000000000), orderedInterval (-25914207498 / 1000000000000) (-25914206336 / 1000000000000)))) (orderedInterval (2609481106 / 1000000000000) (2609483326 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2059148831254489 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12097005503 / 1000000000000) (12097005504 / 1000000000000), orderedInterval (33008377342 / 1000000000000) (33008377343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1819320440132269 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3150077165 / 1000000000000) (-3150077164 / 1000000000000), orderedInterval (-37276086495 / 1000000000000) (-37276086494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (527309974970631 / 800000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5815009325 / 1000000000000) (5815009326 / 1000000000000), orderedInterval (30524649797 / 1000000000000) (30524649798 / 1000000000000)))) (orderedInterval (4716995175 / 1000000000000) (4716995225 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks1_2 :
    compactCertificate485.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1458567141572357 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35206923356 / 1000000000000) (35206923357 / 1000000000000), orderedInterval (22453924820 / 1000000000000) (22453924821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1236443519099677 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40883758990 / 1000000000000) (40883782407 / 1000000000000), orderedInterval (-19764739312 / 1000000000000) (-19764715895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (773708944339231 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-30801563614 / 1000000000000) (-30801557600 / 1000000000000), orderedInterval (48479315499 / 1000000000000) (48479321512 / 1000000000000)))) (orderedInterval (-1845910001 / 1000000000000) (-1845908662 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (416103243505377 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70997824687 / 1000000000000) (-70997824686 / 1000000000000), orderedInterval (-32508235909 / 1000000000000) (-32508235908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1129801249727131 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22423926976 / 1000000000000) (22423926977 / 1000000000000), orderedInterval (41806298653 / 1000000000000) (41806298654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1542647016822587 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1256531495 / 1000000000000) (-1256531493 / 1000000000000), orderedInterval (-40608013095 / 1000000000000) (-40608013094 / 1000000000000)))) (orderedInterval (2790436008 / 1000000000000) (2790436047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (652291055660769 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29657248739 / 1000000000000) (29657248740 / 1000000000000), orderedInterval (54903229212 / 1000000000000) (54903229213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2651526927144449 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22033304294 / 1000000000000) (-22033304293 / 1000000000000), orderedInterval (-21775939803 / 1000000000000) (-21775939802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1771097104799791 / 4000000000000) 1 (IntervalRat.scale (713 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21248128246 / 1000000000000) (-21248128245 / 1000000000000), orderedInterval (-31381657177 / 1000000000000) (-31381657176 / 1000000000000)))) (orderedInterval (10760353536 / 1000000000000) (10760353676 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks1 :
    compactCertificate485.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate485.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate485_chunkChecks1_0
    compactCertificate485_chunkChecks1_1 compactCertificate485_chunkChecks1_2

theorem compactCertificate485_chunkChecks2_0 :
    compactCertificate485.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (713 / 2) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31928737321 / 1000000000000) (-31928693332 / 1000000000000), orderedInterval (27727000762 / 1000000000000) (27727044751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1050385145853413 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24147135921 / 1000000000000) (-24147133614 / 1000000000000), orderedInterval (42955731441 / 1000000000000) (42955733747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (339672974644229 / 800000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36882082111 / 1000000000000) (-36882082108 / 1000000000000), orderedInterval (-11749879377 / 1000000000000) (-11749879374 / 1000000000000)))) (orderedInterval (15818136193 / 1000000000000) (15818153722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (306499765862191 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82479004121 / 1000000000000) (82479010940 / 1000000000000), orderedInterval (-39337128136 / 1000000000000) (-39337121316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (823301483864227 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37292622783 / 1000000000000) (-37292593601 / 1000000000000), orderedInterval (41349169993 / 1000000000000) (41349199175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2235423683638359 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14302760156 / 1000000000000) (14302760157 / 1000000000000), orderedInterval (30558098924 / 1000000000000) (30558098925 / 1000000000000)))) (orderedInterval (3000720246 / 1000000000000) (3000720674 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1646602967729167 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30489364613 / 1000000000000) (-30489364612 / 1000000000000), orderedInterval (-24800499700 / 1000000000000) (-24800499699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2821482250652491 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19412536252 / 1000000000000) (19412537816 / 1000000000000), orderedInterval (-22941600744 / 1000000000000) (-22941599180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2078291055660769 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31899514700 / 1000000000000) (-31899465440 / 1000000000000), orderedInterval (14442390206 / 1000000000000) (14442439466 / 1000000000000)))) (orderedInterval (3976268991 / 1000000000000) (3976271776 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks2_1 :
    compactCertificate485.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3188632935914287 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-595068181 / 1000000000000) (-595068180 / 1000000000000), orderedInterval (28253826133 / 1000000000000) (28253826134 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1840958083896823 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26405545628 / 1000000000000) (26405560121 / 1000000000000), orderedInterval (-26219962181 / 1000000000000) (-26219947688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3266812425603107 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17430731766 / 1000000000000) (17430731767 / 1000000000000), orderedInterval (21799171704 / 1000000000000) (21799171705 / 1000000000000)))) (orderedInterval (-16775181810 / 1000000000000) (-16775179387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3052279927760783 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12516761319 / 1000000000000) (-12516761318 / 1000000000000), orderedInterval (-26022901558 / 1000000000000) (-26022901557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2178250980335039 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32844722431 / 1000000000000) (-32844707616 / 1000000000000), orderedInterval (9531300302 / 1000000000000) (9531315117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2469904451592681 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18980341538 / 1000000000000) (18980342700 / 1000000000000), orderedInterval (-25914207498 / 1000000000000) (-25914206336 / 1000000000000)))) (orderedInterval (6492641809 / 1000000000000) (6492645216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2059148831254489 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12097005503 / 1000000000000) (12097005504 / 1000000000000), orderedInterval (33008377342 / 1000000000000) (33008377343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1819320440132269 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3150077165 / 1000000000000) (-3150077164 / 1000000000000), orderedInterval (-37276086495 / 1000000000000) (-37276086494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (527309974970631 / 800000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5815009325 / 1000000000000) (5815009326 / 1000000000000), orderedInterval (30524649797 / 1000000000000) (30524649798 / 1000000000000)))) (orderedInterval (-1106904231 / 1000000000000) (-1106904157 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks2_2 :
    compactCertificate485.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1458567141572357 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35206923356 / 1000000000000) (35206923357 / 1000000000000), orderedInterval (22453924820 / 1000000000000) (22453924821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1236443519099677 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40883758990 / 1000000000000) (40883782407 / 1000000000000), orderedInterval (-19764739312 / 1000000000000) (-19764715895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (773708944339231 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-30801563614 / 1000000000000) (-30801557600 / 1000000000000), orderedInterval (48479315499 / 1000000000000) (48479321512 / 1000000000000)))) (orderedInterval (7929465057 / 1000000000000) (7929466194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (416103243505377 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70997824687 / 1000000000000) (-70997824686 / 1000000000000), orderedInterval (-32508235909 / 1000000000000) (-32508235908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1129801249727131 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22423926976 / 1000000000000) (22423926977 / 1000000000000), orderedInterval (41806298653 / 1000000000000) (41806298654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1542647016822587 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1256531495 / 1000000000000) (-1256531493 / 1000000000000), orderedInterval (-40608013095 / 1000000000000) (-40608013094 / 1000000000000)))) (orderedInterval (87188299 / 1000000000000) (87188338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (652291055660769 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29657248739 / 1000000000000) (29657248740 / 1000000000000), orderedInterval (54903229212 / 1000000000000) (54903229213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2651526927144449 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22033304294 / 1000000000000) (-22033304293 / 1000000000000), orderedInterval (-21775939803 / 1000000000000) (-21775939802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1771097104799791 / 4000000000000) 2 (IntervalRat.scale (713 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21248128246 / 1000000000000) (-21248128245 / 1000000000000), orderedInterval (-31381657177 / 1000000000000) (-31381657176 / 1000000000000)))) (orderedInterval (-12418455486 / 1000000000000) (-12418455281 / 1000000000000))) = true
  rfl'

theorem compactCertificate485_chunkChecks2 :
    compactCertificate485.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate485.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate485_chunkChecks2_0
    compactCertificate485_chunkChecks2_1 compactCertificate485_chunkChecks2_2

theorem compactCertificate485_chunkChecks3_0 :
    compactCertificate485.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (713 / 2) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31928737321 / 1000000000000) (-31928693332 / 1000000000000), orderedInterval (27727000762 / 1000000000000) (27727044751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1050385145853413 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24147135921 / 1000000000000) (-24147133614 / 1000000000000), orderedInterval (42955731441 / 1000000000000) (42955733747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (339672974644229 / 800000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36882082111 / 1000000000000) (-36882082108 / 1000000000000), orderedInterval (-11749879377 / 1000000000000) (-11749879374 / 1000000000000)))) (orderedInterval (-10029446275 / 1000000000000) (-10029428744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (306499765862191 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82479004121 / 1000000000000) (82479010940 / 1000000000000), orderedInterval (-39337128136 / 1000000000000) (-39337121316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (823301483864227 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37292622783 / 1000000000000) (-37292593601 / 1000000000000), orderedInterval (41349169993 / 1000000000000) (41349199175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2235423683638359 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14302760156 / 1000000000000) (14302760157 / 1000000000000), orderedInterval (30558098924 / 1000000000000) (30558098925 / 1000000000000)))) (orderedInterval (8065393473 / 1000000000000) (8065393781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1646602967729167 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30489364613 / 1000000000000) (-30489364612 / 1000000000000), orderedInterval (-24800499700 / 1000000000000) (-24800499699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2821482250652491 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19412536252 / 1000000000000) (19412537816 / 1000000000000), orderedInterval (-22941600744 / 1000000000000) (-22941599180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2078291055660769 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31899514700 / 1000000000000) (-31899465440 / 1000000000000), orderedInterval (14442390206 / 1000000000000) (14442439466 / 1000000000000)))) (orderedInterval (-6572783397 / 1000000000000) (-6572779217 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate485_chunkChecks3_1 :
    compactCertificate485.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3188632935914287 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-595068181 / 1000000000000) (-595068180 / 1000000000000), orderedInterval (28253826133 / 1000000000000) (28253826134 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1840958083896823 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26405545628 / 1000000000000) (26405560121 / 1000000000000), orderedInterval (-26219962181 / 1000000000000) (-26219947688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3266812425603107 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17430731766 / 1000000000000) (17430731767 / 1000000000000), orderedInterval (21799171704 / 1000000000000) (21799171705 / 1000000000000)))) (orderedInterval (23098419243 / 1000000000000) (23098422938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3052279927760783 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12516761319 / 1000000000000) (-12516761318 / 1000000000000), orderedInterval (-26022901558 / 1000000000000) (-26022901557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2178250980335039 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32844722431 / 1000000000000) (-32844707616 / 1000000000000), orderedInterval (9531300302 / 1000000000000) (9531315117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2469904451592681 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18980341538 / 1000000000000) (18980342700 / 1000000000000), orderedInterval (-25914207498 / 1000000000000) (-25914206336 / 1000000000000)))) (orderedInterval (-8519122846 / 1000000000000) (-8519117619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2059148831254489 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12097005503 / 1000000000000) (12097005504 / 1000000000000), orderedInterval (33008377342 / 1000000000000) (33008377343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1819320440132269 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3150077165 / 1000000000000) (-3150077164 / 1000000000000), orderedInterval (-37276086495 / 1000000000000) (-37276086494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (527309974970631 / 800000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5815009325 / 1000000000000) (5815009326 / 1000000000000), orderedInterval (30524649797 / 1000000000000) (30524649798 / 1000000000000)))) (orderedInterval (-10514258164 / 1000000000000) (-10514258050 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate485_chunkChecks3_2 :
    compactCertificate485.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1458567141572357 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35206923356 / 1000000000000) (35206923357 / 1000000000000), orderedInterval (22453924820 / 1000000000000) (22453924821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1236443519099677 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40883758990 / 1000000000000) (40883782407 / 1000000000000), orderedInterval (-19764739312 / 1000000000000) (-19764715895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (773708944339231 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-30801563614 / 1000000000000) (-30801557600 / 1000000000000), orderedInterval (48479315499 / 1000000000000) (48479321512 / 1000000000000)))) (orderedInterval (2838267674 / 1000000000000) (2838268649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (416103243505377 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70997824687 / 1000000000000) (-70997824686 / 1000000000000), orderedInterval (-32508235909 / 1000000000000) (-32508235908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1129801249727131 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22423926976 / 1000000000000) (22423926977 / 1000000000000), orderedInterval (41806298653 / 1000000000000) (41806298654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1542647016822587 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1256531495 / 1000000000000) (-1256531493 / 1000000000000), orderedInterval (-40608013095 / 1000000000000) (-40608013094 / 1000000000000)))) (orderedInterval (-3483490779 / 1000000000000) (-3483490739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (652291055660769 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29657248739 / 1000000000000) (29657248740 / 1000000000000), orderedInterval (54903229212 / 1000000000000) (54903229213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2651526927144449 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22033304294 / 1000000000000) (-22033304293 / 1000000000000), orderedInterval (-21775939803 / 1000000000000) (-21775939802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1771097104799791 / 4000000000000) 3 (IntervalRat.scale (713 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21248128246 / 1000000000000) (-21248128245 / 1000000000000), orderedInterval (-31381657177 / 1000000000000) (-31381657176 / 1000000000000)))) (orderedInterval (-22673209554 / 1000000000000) (-22673209238 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate485_chunkChecks3 :
    compactCertificate485.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate485.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate485_chunkChecks3_0
    compactCertificate485_chunkChecks3_1 compactCertificate485_chunkChecks3_2

theorem compactCertificate485_chunkChecks4_0 :
    compactCertificate485.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (713 / 2) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31928737321 / 1000000000000) (-31928693332 / 1000000000000), orderedInterval (27727000762 / 1000000000000) (27727044751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1050385145853413 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-24147135921 / 1000000000000) (-24147133614 / 1000000000000), orderedInterval (42955731441 / 1000000000000) (42955733747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (339672974644229 / 800000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36882082111 / 1000000000000) (-36882082108 / 1000000000000), orderedInterval (-11749879377 / 1000000000000) (-11749879374 / 1000000000000)))) (orderedInterval (-17019997762 / 1000000000000) (-17019980178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (306499765862191 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82479004121 / 1000000000000) (82479010940 / 1000000000000), orderedInterval (-39337128136 / 1000000000000) (-39337121316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (823301483864227 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37292622783 / 1000000000000) (-37292593601 / 1000000000000), orderedInterval (41349169993 / 1000000000000) (41349199175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2235423683638359 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14302760156 / 1000000000000) (14302760157 / 1000000000000), orderedInterval (30558098924 / 1000000000000) (30558098925 / 1000000000000)))) (orderedInterval (-6338694808 / 1000000000000) (-6338694532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1646602967729167 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30489364613 / 1000000000000) (-30489364612 / 1000000000000), orderedInterval (-24800499700 / 1000000000000) (-24800499699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2821482250652491 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19412536252 / 1000000000000) (19412537816 / 1000000000000), orderedInterval (-22941600744 / 1000000000000) (-22941599180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2078291055660769 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31899514700 / 1000000000000) (-31899465440 / 1000000000000), orderedInterval (14442390206 / 1000000000000) (14442439466 / 1000000000000)))) (orderedInterval (-12618090765 / 1000000000000) (-12618084423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate485_chunkChecks4_1 :
    compactCertificate485.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3188632935914287 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-595068181 / 1000000000000) (-595068180 / 1000000000000), orderedInterval (28253826133 / 1000000000000) (28253826134 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1840958083896823 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26405545628 / 1000000000000) (26405560121 / 1000000000000), orderedInterval (-26219962181 / 1000000000000) (-26219947688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3266812425603107 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17430731766 / 1000000000000) (17430731767 / 1000000000000), orderedInterval (21799171704 / 1000000000000) (21799171705 / 1000000000000)))) (orderedInterval (76197684294 / 1000000000000) (76197690352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3052279927760783 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12516761319 / 1000000000000) (-12516761318 / 1000000000000), orderedInterval (-26022901558 / 1000000000000) (-26022901557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2178250980335039 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32844722431 / 1000000000000) (-32844707616 / 1000000000000), orderedInterval (9531300302 / 1000000000000) (9531315117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2469904451592681 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18980341538 / 1000000000000) (18980342700 / 1000000000000), orderedInterval (-25914207498 / 1000000000000) (-25914206336 / 1000000000000)))) (orderedInterval (-12983365464 / 1000000000000) (-12983357419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2059148831254489 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12097005503 / 1000000000000) (12097005504 / 1000000000000), orderedInterval (33008377342 / 1000000000000) (33008377343 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1819320440132269 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3150077165 / 1000000000000) (-3150077164 / 1000000000000), orderedInterval (-37276086495 / 1000000000000) (-37276086494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (527309974970631 / 800000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5815009325 / 1000000000000) (5815009326 / 1000000000000), orderedInterval (30524649797 / 1000000000000) (30524649798 / 1000000000000)))) (orderedInterval (2883846923 / 1000000000000) (2883847103 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate485_chunkChecks4_2 :
    compactCertificate485.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1458567141572357 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35206923356 / 1000000000000) (35206923357 / 1000000000000), orderedInterval (22453924820 / 1000000000000) (22453924821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1236443519099677 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40883758990 / 1000000000000) (40883782407 / 1000000000000), orderedInterval (-19764739312 / 1000000000000) (-19764715895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (773708944339231 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-30801563614 / 1000000000000) (-30801557600 / 1000000000000), orderedInterval (48479315499 / 1000000000000) (48479321512 / 1000000000000)))) (orderedInterval (-7572156668 / 1000000000000) (-7572155821 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (416103243505377 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70997824687 / 1000000000000) (-70997824686 / 1000000000000), orderedInterval (-32508235909 / 1000000000000) (-32508235908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1129801249727131 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (22423926976 / 1000000000000) (22423926977 / 1000000000000), orderedInterval (41806298653 / 1000000000000) (41806298654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1542647016822587 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1256531495 / 1000000000000) (-1256531493 / 1000000000000), orderedInterval (-40608013095 / 1000000000000) (-40608013094 / 1000000000000)))) (orderedInterval (-39517358 / 1000000000000) (-39517316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (652291055660769 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29657248739 / 1000000000000) (29657248740 / 1000000000000), orderedInterval (54903229212 / 1000000000000) (54903229213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2651526927144449 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22033304294 / 1000000000000) (-22033304293 / 1000000000000), orderedInterval (-21775939803 / 1000000000000) (-21775939802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1771097104799791 / 4000000000000) 4 (IntervalRat.scale (713 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21248128246 / 1000000000000) (-21248128245 / 1000000000000), orderedInterval (-31381657177 / 1000000000000) (-31381657176 / 1000000000000)))) (orderedInterval (31061178010 / 1000000000000) (31061178518 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate485_chunkChecks4 :
    compactCertificate485.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate485.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate485_chunkChecks4_0
    compactCertificate485_chunkChecks4_1 compactCertificate485_chunkChecks4_2

theorem compactCertificate485_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate485.chunkCheck r b = true :=
  compactCertificate485.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate485_chunkChecks0
    · exact compactCertificate485_chunkChecks1
    · exact compactCertificate485_chunkChecks2
    · exact compactCertificate485_chunkChecks3
    · exact compactCertificate485_chunkChecks4)

theorem compactCertificate485_coefficient0 :
    compactCertificate485.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate485_coefficient1 :
    compactCertificate485.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate485_coefficient2 :
    compactCertificate485.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate485_coefficient3 :
    compactCertificate485.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate485_coefficient4 :
    compactCertificate485.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate485_coefficients : ∀ r : Fin 5,
    compactCertificate485.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate485_coefficient0
  · exact compactCertificate485_coefficient1
  · exact compactCertificate485_coefficient2
  · exact compactCertificate485_coefficient3
  · exact compactCertificate485_coefficient4

theorem compactCertificate485_lower : (1 : ℚ) ≤ compactCertificate485.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate485, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate485_proves {t : ℝ} (ht : t ∈ compactCertificate485.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate485.proves compactCertificate485_states compactCertificate485_chunks
    compactCertificate485_coefficients compactCertificate485_lower ht

end Erdos232
