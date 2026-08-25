/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate269 : CompactCertificate where
  left := 143
  right := 144
  center := 287 / 2
  grid := fun i =>
    match i.val with
    | 0 => 46
    | 1 => 34
    | 2 => 54
    | 3 => 10
    | 4 => 26
    | 5 => 72
    | 6 => 53
    | 7 => 90
    | 8 => 67
    | 9 => 102
    | 10 => 59
    | 11 => 105
    | 12 => 98
    | 13 => 70
    | 14 => 79
    | 15 => 66
    | 16 => 58
    | 17 => 84
    | 18 => 47
    | 19 => 40
    | 20 => 25
    | 21 => 13
    | 22 => 36
    | 23 => 49
    | 24 => 21
    | 25 => 85
    | _ => 57
  point := fun i =>
    match i.val with
    | 0 => 287 / 2
    | 1 => 422805802047587 / 4000000000000
    | 2 => 136726709288771 / 800000000000
    | 3 => 123373678544809 / 4000000000000
    | 4 => 331399054514773 / 4000000000000
    | 5 => 899812899304641 / 4000000000000
    | 6 => 662798109029833 / 4000000000000
    | 7 => 1135715856854509 / 4000000000000
    | 8 => 836563159852231 / 4000000000000
    | 9 => 1283503019084713 / 4000000000000
    | 10 => 741030813574177 / 4000000000000
    | 11 => 1314972182535893 / 4000000000000
    | 12 => 1228617586630217 / 4000000000000
    | 13 => 876799482967961 / 4000000000000
    | 14 => 994197163544319 / 4000000000000
    | 15 => 828857944698511 / 4000000000000
    | 16 => 732321130880731 / 4000000000000
    | 17 => 212255207316369 / 800000000000
    | 18 => 587109073816643 / 4000000000000
    | 19 => 497698863929323 / 4000000000000
    | 20 => 311436840147769 / 4000000000000
    | 21 => 167491768423623 / 4000000000000
    | 22 => 454772733059869 / 4000000000000
    | 23 => 620953287276413 / 4000000000000
    | 24 => 262563159852231 / 4000000000000
    | 25 => 1067304667728551 / 4000000000000
    | _ => 712910054807209 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-15102598980 / 1000000000000) (-15102598836 / 1000000000000), orderedInterval (64924112896 / 1000000000000) (64924113041 / 1000000000000))
    | 1 => (orderedInterval (-25036464349 / 1000000000000) (-25036463675 / 1000000000000), orderedInterval (73576163231 / 1000000000000) (73576163905 / 1000000000000))
    | 2 => (orderedInterval (54240247127 / 1000000000000) (54240262772 / 1000000000000), orderedInterval (-28139105487 / 1000000000000) (-28139089843 / 1000000000000))
    | 3 => (orderedInterval (29784069155 / 1000000000000) (29784069156 / 1000000000000), orderedInterval (140072484110 / 1000000000000) (140072484111 / 1000000000000))
    | 4 => (orderedInterval (81357518783 / 1000000000000) (81357522602 / 1000000000000), orderedInterval (-33123463601 / 1000000000000) (-33123459782 / 1000000000000))
    | 5 => (orderedInterval (-23455020181 / 1000000000000) (-23455018664 / 1000000000000), orderedInterval (47800177838 / 1000000000000) (47800179355 / 1000000000000))
    | 6 => (orderedInterval (1254441284 / 1000000000000) (1254441290 / 1000000000000), orderedInterval (-61975206588 / 1000000000000) (-61975206582 / 1000000000000))
    | 7 => (orderedInterval (43617653929 / 1000000000000) (43617666885 / 1000000000000), orderedInterval (-18507145225 / 1000000000000) (-18507132270 / 1000000000000))
    | 8 => (orderedInterval (29358904368 / 1000000000000) (29358909588 / 1000000000000), orderedInterval (-46782453585 / 1000000000000) (-46782448364 / 1000000000000))
    | 9 => (orderedInterval (41803634385 / 1000000000000) (41803634387 / 1000000000000), orderedInterval (15312161940 / 1000000000000) (15312161942 / 1000000000000))
    | 10 => (orderedInterval (-37244609642 / 1000000000000) (-37244609641 / 1000000000000), orderedInterval (-45168039886 / 1000000000000) (-45168039885 / 1000000000000))
    | 11 => (orderedInterval (14640776377 / 1000000000000) (14640776559 / 1000000000000), orderedInterval (-41521380769 / 1000000000000) (-41521380587 / 1000000000000))
    | 12 => (orderedInterval (2880239199 / 1000000000000) (2880239201 / 1000000000000), orderedInterval (45430370732 / 1000000000000) (45430370734 / 1000000000000))
    | 13 => (orderedInterval (3942021037 / 1000000000000) (3942021038 / 1000000000000), orderedInterval (53738165710 / 1000000000000) (53738165712 / 1000000000000))
    | 14 => (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))
    | 15 => (orderedInterval (33727818006 / 1000000000000) (33727818007 / 1000000000000), orderedInterval (43903967236 / 1000000000000) (43903967237 / 1000000000000))
    | 16 => (orderedInterval (58770970543 / 1000000000000) (58770970734 / 1000000000000), orderedInterval (-4980390339 / 1000000000000) (-4980390148 / 1000000000000))
    | 17 => (orderedInterval (39308720941 / 1000000000000) (39308824167 / 1000000000000), orderedInterval (-29302013876 / 1000000000000) (-29301910650 / 1000000000000))
    | 18 => (orderedInterval (6118585066 / 1000000000000) (6118585085 / 1000000000000), orderedInterval (-65594513021 / 1000000000000) (-65594513002 / 1000000000000))
    | 19 => (orderedInterval (-31408582958 / 1000000000000) (-31408580335 / 1000000000000), orderedInterval (64391537622 / 1000000000000) (64391540245 / 1000000000000))
    | 20 => (orderedInterval (-9313923389 / 1000000000000) (-9313923387 / 1000000000000), orderedInterval (-89884430570 / 1000000000000) (-89884430568 / 1000000000000))
    | 21 => (orderedInterval (-119650656347 / 1000000000000) (-119650655718 / 1000000000000), orderedInterval (31200519589 / 1000000000000) (31200520218 / 1000000000000))
    | 22 => (orderedInterval (73473332435 / 1000000000000) (73473332438 / 1000000000000), orderedInterval (13856919210 / 1000000000000) (13856919212 / 1000000000000))
    | 23 => (orderedInterval (-55761077737 / 1000000000000) (-55761056925 / 1000000000000), orderedInterval (31669445229 / 1000000000000) (31669466042 / 1000000000000))
    | 24 => (orderedInterval (-42909614168 / 1000000000000) (-42909614167 / 1000000000000), orderedInterval (-88315587326 / 1000000000000) (-88315587325 / 1000000000000))
    | 25 => (orderedInterval (-26593488582 / 1000000000000) (-26593488581 / 1000000000000), orderedInterval (-40921927587 / 1000000000000) (-40921927586 / 1000000000000))
    | _ => (orderedInterval (3498518064 / 1000000000000) (3498518073 / 1000000000000), orderedInterval (-59673240306 / 1000000000000) (-59673240297 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-3036553286 / 1000000000000) (-3036552294 / 1000000000000)
      | 1 => orderedInterval (4314777875 / 1000000000000) (4314778140 / 1000000000000)
      | 2 => orderedInterval (-635796572 / 1000000000000) (-635796037 / 1000000000000)
      | 3 => orderedInterval (-8106247585 / 1000000000000) (-8106247502 / 1000000000000)
      | 4 => orderedInterval (554372003 / 1000000000000) (554372021 / 1000000000000)
      | 5 => orderedInterval (-1967331129 / 1000000000000) (-1967328460 / 1000000000000)
      | 6 => orderedInterval (496191436 / 1000000000000) (496191624 / 1000000000000)
      | 7 => orderedInterval (4815948387 / 1000000000000) (4815950012 / 1000000000000)
      | _ => orderedInterval (1249669183 / 1000000000000) (1249669225 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (24272026577 / 1000000000000) (24272027744 / 1000000000000)
      | 1 => orderedInterval (-6351801333 / 1000000000000) (-6351801063 / 1000000000000)
      | 2 => orderedInterval (-518373187 / 1000000000000) (-518372198 / 1000000000000)
      | 3 => orderedInterval (-23926291724 / 1000000000000) (-23926291545 / 1000000000000)
      | 4 => orderedInterval (6187872234 / 1000000000000) (6187872263 / 1000000000000)
      | 5 => orderedInterval (-291425626 / 1000000000000) (-291420705 / 1000000000000)
      | 6 => orderedInterval (5979819597 / 1000000000000) (5979819763 / 1000000000000)
      | 7 => orderedInterval (-3042832255 / 1000000000000) (-3042830510 / 1000000000000)
      | _ => orderedInterval (19856224007 / 1000000000000) (19856224066 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (1428726487 / 1000000000000) (1428727871 / 1000000000000)
      | 1 => orderedInterval (-5028512809 / 1000000000000) (-5028512467 / 1000000000000)
      | 2 => orderedInterval (3763289706 / 1000000000000) (3763291571 / 1000000000000)
      | 3 => orderedInterval (30983028345 / 1000000000000) (30983028736 / 1000000000000)
      | 4 => orderedInterval (-1375489917 / 1000000000000) (-1375489870 / 1000000000000)
      | 5 => orderedInterval (1223799572 / 1000000000000) (1223808689 / 1000000000000)
      | 6 => orderedInterval (-265412327 / 1000000000000) (-265412179 / 1000000000000)
      | 7 => orderedInterval (-4121783505 / 1000000000000) (-4121781609 / 1000000000000)
      | _ => orderedInterval (-6556168920 / 1000000000000) (-6556168834 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-23226815821 / 1000000000000) (-23226814185 / 1000000000000)
      | 1 => orderedInterval (13373088597 / 1000000000000) (13373089083 / 1000000000000)
      | 2 => orderedInterval (-947757756 / 1000000000000) (-947754212 / 1000000000000)
      | 3 => orderedInterval (108368993662 / 1000000000000) (108368994532 / 1000000000000)
      | 4 => orderedInterval (-10602476257 / 1000000000000) (-10602476178 / 1000000000000)
      | 5 => orderedInterval (2614959410 / 1000000000000) (2614976247 / 1000000000000)
      | 6 => orderedInterval (-8377858967 / 1000000000000) (-8377858834 / 1000000000000)
      | 7 => orderedInterval (3272010360 / 1000000000000) (3272012409 / 1000000000000)
      | _ => orderedInterval (-42768208772 / 1000000000000) (-42768208641 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (673178580 / 1000000000000) (673180527 / 1000000000000)
      | 1 => orderedInterval (10212135238 / 1000000000000) (10212135975 / 1000000000000)
      | 2 => orderedInterval (-17404137690 / 1000000000000) (-17404130863 / 1000000000000)
      | 3 => orderedInterval (-137548739895 / 1000000000000) (-137548737938 / 1000000000000)
      | 4 => orderedInterval (3188184807 / 1000000000000) (3188184945 / 1000000000000)
      | 5 => orderedInterval (4507602116 / 1000000000000) (4507633336 / 1000000000000)
      | 6 => orderedInterval (24485307 / 1000000000000) (24485427 / 1000000000000)
      | 7 => orderedInterval (5166275084 / 1000000000000) (5166277314 / 1000000000000)
      | _ => orderedInterval (24899542647 / 1000000000000) (24899542857 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2314969688 / 1000000000000) (-2314963271 / 1000000000000)
    | 1 => orderedInterval (22165218290 / 1000000000000) (22165227815 / 1000000000000)
    | 2 => orderedInterval (20051476632 / 1000000000000) (20051491908 / 1000000000000)
    | 3 => orderedInterval (41705934456 / 1000000000000) (41705960221 / 1000000000000)
    | _ => orderedInterval (-106281473806 / 1000000000000) (-106281428420 / 1000000000000)

theorem compactCertificate269_stateChecks0 :
    compactCertificate269.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (287 / 2)) (orderedInterval (-15102598980 / 1000000000000) (-15102598836 / 1000000000000), orderedInterval (64924112896 / 1000000000000) (64924113041 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (422805802047587 / 4000000000000)) (orderedInterval (-25036464349 / 1000000000000) (-25036463675 / 1000000000000), orderedInterval (73576163231 / 1000000000000) (73576163905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (136726709288771 / 800000000000)) (orderedInterval (54240247127 / 1000000000000) (54240262772 / 1000000000000), orderedInterval (-28139105487 / 1000000000000) (-28139089843 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_stateChecks1 :
    compactCertificate269.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (123373678544809 / 4000000000000)) (orderedInterval (29784069155 / 1000000000000) (29784069156 / 1000000000000), orderedInterval (140072484110 / 1000000000000) (140072484111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (331399054514773 / 4000000000000)) (orderedInterval (81357518783 / 1000000000000) (81357522602 / 1000000000000), orderedInterval (-33123463601 / 1000000000000) (-33123459782 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (899812899304641 / 4000000000000)) (orderedInterval (-23455020181 / 1000000000000) (-23455018664 / 1000000000000), orderedInterval (47800177838 / 1000000000000) (47800179355 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_stateChecks2 :
    compactCertificate269.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (662798109029833 / 4000000000000)) (orderedInterval (1254441284 / 1000000000000) (1254441290 / 1000000000000), orderedInterval (-61975206588 / 1000000000000) (-61975206582 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1135715856854509 / 4000000000000)) (orderedInterval (43617653929 / 1000000000000) (43617666885 / 1000000000000), orderedInterval (-18507145225 / 1000000000000) (-18507132270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (836563159852231 / 4000000000000)) (orderedInterval (29358904368 / 1000000000000) (29358909588 / 1000000000000), orderedInterval (-46782453585 / 1000000000000) (-46782448364 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_stateChecks3 :
    compactCertificate269.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1283503019084713 / 4000000000000)) (orderedInterval (41803634385 / 1000000000000) (41803634387 / 1000000000000), orderedInterval (15312161940 / 1000000000000) (15312161942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (741030813574177 / 4000000000000)) (orderedInterval (-37244609642 / 1000000000000) (-37244609641 / 1000000000000), orderedInterval (-45168039886 / 1000000000000) (-45168039885 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1314972182535893 / 4000000000000)) (orderedInterval (14640776377 / 1000000000000) (14640776559 / 1000000000000), orderedInterval (-41521380769 / 1000000000000) (-41521380587 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_stateChecks4 :
    compactCertificate269.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1228617586630217 / 4000000000000)) (orderedInterval (2880239199 / 1000000000000) (2880239201 / 1000000000000), orderedInterval (45430370732 / 1000000000000) (45430370734 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (876799482967961 / 4000000000000)) (orderedInterval (3942021037 / 1000000000000) (3942021038 / 1000000000000), orderedInterval (53738165710 / 1000000000000) (53738165712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (994197163544319 / 4000000000000)) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_stateChecks5 :
    compactCertificate269.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (828857944698511 / 4000000000000)) (orderedInterval (33727818006 / 1000000000000) (33727818007 / 1000000000000), orderedInterval (43903967236 / 1000000000000) (43903967237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (732321130880731 / 4000000000000)) (orderedInterval (58770970543 / 1000000000000) (58770970734 / 1000000000000), orderedInterval (-4980390339 / 1000000000000) (-4980390148 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (212255207316369 / 800000000000)) (orderedInterval (39308720941 / 1000000000000) (39308824167 / 1000000000000), orderedInterval (-29302013876 / 1000000000000) (-29301910650 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_stateChecks6 :
    compactCertificate269.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (587109073816643 / 4000000000000)) (orderedInterval (6118585066 / 1000000000000) (6118585085 / 1000000000000), orderedInterval (-65594513021 / 1000000000000) (-65594513002 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (497698863929323 / 4000000000000)) (orderedInterval (-31408582958 / 1000000000000) (-31408580335 / 1000000000000), orderedInterval (64391537622 / 1000000000000) (64391540245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (311436840147769 / 4000000000000)) (orderedInterval (-9313923389 / 1000000000000) (-9313923387 / 1000000000000), orderedInterval (-89884430570 / 1000000000000) (-89884430568 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_stateChecks7 :
    compactCertificate269.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (167491768423623 / 4000000000000)) (orderedInterval (-119650656347 / 1000000000000) (-119650655718 / 1000000000000), orderedInterval (31200519589 / 1000000000000) (31200520218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (454772733059869 / 4000000000000)) (orderedInterval (73473332435 / 1000000000000) (73473332438 / 1000000000000), orderedInterval (13856919210 / 1000000000000) (13856919212 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (620953287276413 / 4000000000000)) (orderedInterval (-55761077737 / 1000000000000) (-55761056925 / 1000000000000), orderedInterval (31669445229 / 1000000000000) (31669466042 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_stateChecks8 :
    compactCertificate269.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (262563159852231 / 4000000000000)) (orderedInterval (-42909614168 / 1000000000000) (-42909614167 / 1000000000000), orderedInterval (-88315587326 / 1000000000000) (-88315587325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1067304667728551 / 4000000000000)) (orderedInterval (-26593488582 / 1000000000000) (-26593488581 / 1000000000000), orderedInterval (-40921927587 / 1000000000000) (-40921927586 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (712910054807209 / 4000000000000)) (orderedInterval (3498518064 / 1000000000000) (3498518073 / 1000000000000), orderedInterval (-59673240306 / 1000000000000) (-59673240297 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState021, besselGridState025, besselGridState026, besselGridState034, besselGridState036, besselGridState040, besselGridState046, besselGridState047, besselGridState049, besselGridState053, besselGridState054, besselGridState057, besselGridState058, besselGridState059, besselGridState066, besselGridState067, besselGridState070, besselGridState072, besselGridState079, besselGridState084, besselGridState085, besselGridState090, besselGridState098, besselGridState102, besselGridState105, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate269_states : ∀ j,
    BesselStateValid (compactCertificate269.point j) (compactCertificate269.state j) :=
  compactCertificate269.statesValid_of_checks3 compactCertificate269_stateChecks0
    compactCertificate269_stateChecks1 compactCertificate269_stateChecks2
    compactCertificate269_stateChecks3 compactCertificate269_stateChecks4
    compactCertificate269_stateChecks5 compactCertificate269_stateChecks6
    compactCertificate269_stateChecks7 compactCertificate269_stateChecks8

theorem compactCertificate269_chunkChecks0_0 :
    compactCertificate269.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (287 / 2) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15102598980 / 1000000000000) (-15102598836 / 1000000000000), orderedInterval (64924112896 / 1000000000000) (64924113041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (422805802047587 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25036464349 / 1000000000000) (-25036463675 / 1000000000000), orderedInterval (73576163231 / 1000000000000) (73576163905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (136726709288771 / 800000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54240247127 / 1000000000000) (54240262772 / 1000000000000), orderedInterval (-28139105487 / 1000000000000) (-28139089843 / 1000000000000)))) (orderedInterval (-3036553286 / 1000000000000) (-3036552294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (123373678544809 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (29784069155 / 1000000000000) (29784069156 / 1000000000000), orderedInterval (140072484110 / 1000000000000) (140072484111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (331399054514773 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81357518783 / 1000000000000) (81357522602 / 1000000000000), orderedInterval (-33123463601 / 1000000000000) (-33123459782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (899812899304641 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23455020181 / 1000000000000) (-23455018664 / 1000000000000), orderedInterval (47800177838 / 1000000000000) (47800179355 / 1000000000000)))) (orderedInterval (4314777875 / 1000000000000) (4314778140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (662798109029833 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1254441284 / 1000000000000) (1254441290 / 1000000000000), orderedInterval (-61975206588 / 1000000000000) (-61975206582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1135715856854509 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (43617653929 / 1000000000000) (43617666885 / 1000000000000), orderedInterval (-18507145225 / 1000000000000) (-18507132270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (836563159852231 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29358904368 / 1000000000000) (29358909588 / 1000000000000), orderedInterval (-46782453585 / 1000000000000) (-46782448364 / 1000000000000)))) (orderedInterval (-635796572 / 1000000000000) (-635796037 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks0_1 :
    compactCertificate269.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1283503019084713 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (41803634385 / 1000000000000) (41803634387 / 1000000000000), orderedInterval (15312161940 / 1000000000000) (15312161942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (741030813574177 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37244609642 / 1000000000000) (-37244609641 / 1000000000000), orderedInterval (-45168039886 / 1000000000000) (-45168039885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1314972182535893 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14640776377 / 1000000000000) (14640776559 / 1000000000000), orderedInterval (-41521380769 / 1000000000000) (-41521380587 / 1000000000000)))) (orderedInterval (-8106247585 / 1000000000000) (-8106247502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1228617586630217 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2880239199 / 1000000000000) (2880239201 / 1000000000000), orderedInterval (45430370732 / 1000000000000) (45430370734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (876799482967961 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3942021037 / 1000000000000) (3942021038 / 1000000000000), orderedInterval (53738165710 / 1000000000000) (53738165712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000)))) (orderedInterval (554372003 / 1000000000000) (554372021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (828857944698511 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33727818006 / 1000000000000) (33727818007 / 1000000000000), orderedInterval (43903967236 / 1000000000000) (43903967237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (732321130880731 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58770970543 / 1000000000000) (58770970734 / 1000000000000), orderedInterval (-4980390339 / 1000000000000) (-4980390148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (212255207316369 / 800000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39308720941 / 1000000000000) (39308824167 / 1000000000000), orderedInterval (-29302013876 / 1000000000000) (-29301910650 / 1000000000000)))) (orderedInterval (-1967331129 / 1000000000000) (-1967328460 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks0_2 :
    compactCertificate269.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (587109073816643 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6118585066 / 1000000000000) (6118585085 / 1000000000000), orderedInterval (-65594513021 / 1000000000000) (-65594513002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (497698863929323 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31408582958 / 1000000000000) (-31408580335 / 1000000000000), orderedInterval (64391537622 / 1000000000000) (64391540245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (311436840147769 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9313923389 / 1000000000000) (-9313923387 / 1000000000000), orderedInterval (-89884430570 / 1000000000000) (-89884430568 / 1000000000000)))) (orderedInterval (496191436 / 1000000000000) (496191624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (167491768423623 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-119650656347 / 1000000000000) (-119650655718 / 1000000000000), orderedInterval (31200519589 / 1000000000000) (31200520218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (454772733059869 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (73473332435 / 1000000000000) (73473332438 / 1000000000000), orderedInterval (13856919210 / 1000000000000) (13856919212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (620953287276413 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55761077737 / 1000000000000) (-55761056925 / 1000000000000), orderedInterval (31669445229 / 1000000000000) (31669466042 / 1000000000000)))) (orderedInterval (4815948387 / 1000000000000) (4815950012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (262563159852231 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42909614168 / 1000000000000) (-42909614167 / 1000000000000), orderedInterval (-88315587326 / 1000000000000) (-88315587325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1067304667728551 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26593488582 / 1000000000000) (-26593488581 / 1000000000000), orderedInterval (-40921927587 / 1000000000000) (-40921927586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (712910054807209 / 4000000000000) 0 (IntervalRat.scale (287 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3498518064 / 1000000000000) (3498518073 / 1000000000000), orderedInterval (-59673240306 / 1000000000000) (-59673240297 / 1000000000000)))) (orderedInterval (1249669183 / 1000000000000) (1249669225 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks0 :
    compactCertificate269.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate269.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate269_chunkChecks0_0
    compactCertificate269_chunkChecks0_1 compactCertificate269_chunkChecks0_2

theorem compactCertificate269_chunkChecks1_0 :
    compactCertificate269.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (287 / 2) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15102598980 / 1000000000000) (-15102598836 / 1000000000000), orderedInterval (64924112896 / 1000000000000) (64924113041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (422805802047587 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25036464349 / 1000000000000) (-25036463675 / 1000000000000), orderedInterval (73576163231 / 1000000000000) (73576163905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (136726709288771 / 800000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54240247127 / 1000000000000) (54240262772 / 1000000000000), orderedInterval (-28139105487 / 1000000000000) (-28139089843 / 1000000000000)))) (orderedInterval (24272026577 / 1000000000000) (24272027744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (123373678544809 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (29784069155 / 1000000000000) (29784069156 / 1000000000000), orderedInterval (140072484110 / 1000000000000) (140072484111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (331399054514773 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81357518783 / 1000000000000) (81357522602 / 1000000000000), orderedInterval (-33123463601 / 1000000000000) (-33123459782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (899812899304641 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23455020181 / 1000000000000) (-23455018664 / 1000000000000), orderedInterval (47800177838 / 1000000000000) (47800179355 / 1000000000000)))) (orderedInterval (-6351801333 / 1000000000000) (-6351801063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (662798109029833 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1254441284 / 1000000000000) (1254441290 / 1000000000000), orderedInterval (-61975206588 / 1000000000000) (-61975206582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1135715856854509 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (43617653929 / 1000000000000) (43617666885 / 1000000000000), orderedInterval (-18507145225 / 1000000000000) (-18507132270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (836563159852231 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29358904368 / 1000000000000) (29358909588 / 1000000000000), orderedInterval (-46782453585 / 1000000000000) (-46782448364 / 1000000000000)))) (orderedInterval (-518373187 / 1000000000000) (-518372198 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks1_1 :
    compactCertificate269.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1283503019084713 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (41803634385 / 1000000000000) (41803634387 / 1000000000000), orderedInterval (15312161940 / 1000000000000) (15312161942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (741030813574177 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37244609642 / 1000000000000) (-37244609641 / 1000000000000), orderedInterval (-45168039886 / 1000000000000) (-45168039885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1314972182535893 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14640776377 / 1000000000000) (14640776559 / 1000000000000), orderedInterval (-41521380769 / 1000000000000) (-41521380587 / 1000000000000)))) (orderedInterval (-23926291724 / 1000000000000) (-23926291545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1228617586630217 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2880239199 / 1000000000000) (2880239201 / 1000000000000), orderedInterval (45430370732 / 1000000000000) (45430370734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (876799482967961 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3942021037 / 1000000000000) (3942021038 / 1000000000000), orderedInterval (53738165710 / 1000000000000) (53738165712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000)))) (orderedInterval (6187872234 / 1000000000000) (6187872263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (828857944698511 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33727818006 / 1000000000000) (33727818007 / 1000000000000), orderedInterval (43903967236 / 1000000000000) (43903967237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (732321130880731 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58770970543 / 1000000000000) (58770970734 / 1000000000000), orderedInterval (-4980390339 / 1000000000000) (-4980390148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (212255207316369 / 800000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39308720941 / 1000000000000) (39308824167 / 1000000000000), orderedInterval (-29302013876 / 1000000000000) (-29301910650 / 1000000000000)))) (orderedInterval (-291425626 / 1000000000000) (-291420705 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks1_2 :
    compactCertificate269.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (587109073816643 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6118585066 / 1000000000000) (6118585085 / 1000000000000), orderedInterval (-65594513021 / 1000000000000) (-65594513002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (497698863929323 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31408582958 / 1000000000000) (-31408580335 / 1000000000000), orderedInterval (64391537622 / 1000000000000) (64391540245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (311436840147769 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9313923389 / 1000000000000) (-9313923387 / 1000000000000), orderedInterval (-89884430570 / 1000000000000) (-89884430568 / 1000000000000)))) (orderedInterval (5979819597 / 1000000000000) (5979819763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (167491768423623 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-119650656347 / 1000000000000) (-119650655718 / 1000000000000), orderedInterval (31200519589 / 1000000000000) (31200520218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (454772733059869 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (73473332435 / 1000000000000) (73473332438 / 1000000000000), orderedInterval (13856919210 / 1000000000000) (13856919212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (620953287276413 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55761077737 / 1000000000000) (-55761056925 / 1000000000000), orderedInterval (31669445229 / 1000000000000) (31669466042 / 1000000000000)))) (orderedInterval (-3042832255 / 1000000000000) (-3042830510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (262563159852231 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42909614168 / 1000000000000) (-42909614167 / 1000000000000), orderedInterval (-88315587326 / 1000000000000) (-88315587325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1067304667728551 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26593488582 / 1000000000000) (-26593488581 / 1000000000000), orderedInterval (-40921927587 / 1000000000000) (-40921927586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (712910054807209 / 4000000000000) 1 (IntervalRat.scale (287 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3498518064 / 1000000000000) (3498518073 / 1000000000000), orderedInterval (-59673240306 / 1000000000000) (-59673240297 / 1000000000000)))) (orderedInterval (19856224007 / 1000000000000) (19856224066 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks1 :
    compactCertificate269.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate269.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate269_chunkChecks1_0
    compactCertificate269_chunkChecks1_1 compactCertificate269_chunkChecks1_2

theorem compactCertificate269_chunkChecks2_0 :
    compactCertificate269.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (287 / 2) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15102598980 / 1000000000000) (-15102598836 / 1000000000000), orderedInterval (64924112896 / 1000000000000) (64924113041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (422805802047587 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25036464349 / 1000000000000) (-25036463675 / 1000000000000), orderedInterval (73576163231 / 1000000000000) (73576163905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (136726709288771 / 800000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54240247127 / 1000000000000) (54240262772 / 1000000000000), orderedInterval (-28139105487 / 1000000000000) (-28139089843 / 1000000000000)))) (orderedInterval (1428726487 / 1000000000000) (1428727871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (123373678544809 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (29784069155 / 1000000000000) (29784069156 / 1000000000000), orderedInterval (140072484110 / 1000000000000) (140072484111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (331399054514773 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81357518783 / 1000000000000) (81357522602 / 1000000000000), orderedInterval (-33123463601 / 1000000000000) (-33123459782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (899812899304641 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23455020181 / 1000000000000) (-23455018664 / 1000000000000), orderedInterval (47800177838 / 1000000000000) (47800179355 / 1000000000000)))) (orderedInterval (-5028512809 / 1000000000000) (-5028512467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (662798109029833 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1254441284 / 1000000000000) (1254441290 / 1000000000000), orderedInterval (-61975206588 / 1000000000000) (-61975206582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1135715856854509 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (43617653929 / 1000000000000) (43617666885 / 1000000000000), orderedInterval (-18507145225 / 1000000000000) (-18507132270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (836563159852231 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29358904368 / 1000000000000) (29358909588 / 1000000000000), orderedInterval (-46782453585 / 1000000000000) (-46782448364 / 1000000000000)))) (orderedInterval (3763289706 / 1000000000000) (3763291571 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks2_1 :
    compactCertificate269.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1283503019084713 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (41803634385 / 1000000000000) (41803634387 / 1000000000000), orderedInterval (15312161940 / 1000000000000) (15312161942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (741030813574177 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37244609642 / 1000000000000) (-37244609641 / 1000000000000), orderedInterval (-45168039886 / 1000000000000) (-45168039885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1314972182535893 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14640776377 / 1000000000000) (14640776559 / 1000000000000), orderedInterval (-41521380769 / 1000000000000) (-41521380587 / 1000000000000)))) (orderedInterval (30983028345 / 1000000000000) (30983028736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1228617586630217 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2880239199 / 1000000000000) (2880239201 / 1000000000000), orderedInterval (45430370732 / 1000000000000) (45430370734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (876799482967961 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3942021037 / 1000000000000) (3942021038 / 1000000000000), orderedInterval (53738165710 / 1000000000000) (53738165712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000)))) (orderedInterval (-1375489917 / 1000000000000) (-1375489870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (828857944698511 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33727818006 / 1000000000000) (33727818007 / 1000000000000), orderedInterval (43903967236 / 1000000000000) (43903967237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (732321130880731 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58770970543 / 1000000000000) (58770970734 / 1000000000000), orderedInterval (-4980390339 / 1000000000000) (-4980390148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (212255207316369 / 800000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39308720941 / 1000000000000) (39308824167 / 1000000000000), orderedInterval (-29302013876 / 1000000000000) (-29301910650 / 1000000000000)))) (orderedInterval (1223799572 / 1000000000000) (1223808689 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks2_2 :
    compactCertificate269.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (587109073816643 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6118585066 / 1000000000000) (6118585085 / 1000000000000), orderedInterval (-65594513021 / 1000000000000) (-65594513002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (497698863929323 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31408582958 / 1000000000000) (-31408580335 / 1000000000000), orderedInterval (64391537622 / 1000000000000) (64391540245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (311436840147769 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9313923389 / 1000000000000) (-9313923387 / 1000000000000), orderedInterval (-89884430570 / 1000000000000) (-89884430568 / 1000000000000)))) (orderedInterval (-265412327 / 1000000000000) (-265412179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (167491768423623 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-119650656347 / 1000000000000) (-119650655718 / 1000000000000), orderedInterval (31200519589 / 1000000000000) (31200520218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (454772733059869 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (73473332435 / 1000000000000) (73473332438 / 1000000000000), orderedInterval (13856919210 / 1000000000000) (13856919212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (620953287276413 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55761077737 / 1000000000000) (-55761056925 / 1000000000000), orderedInterval (31669445229 / 1000000000000) (31669466042 / 1000000000000)))) (orderedInterval (-4121783505 / 1000000000000) (-4121781609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (262563159852231 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42909614168 / 1000000000000) (-42909614167 / 1000000000000), orderedInterval (-88315587326 / 1000000000000) (-88315587325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1067304667728551 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26593488582 / 1000000000000) (-26593488581 / 1000000000000), orderedInterval (-40921927587 / 1000000000000) (-40921927586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (712910054807209 / 4000000000000) 2 (IntervalRat.scale (287 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3498518064 / 1000000000000) (3498518073 / 1000000000000), orderedInterval (-59673240306 / 1000000000000) (-59673240297 / 1000000000000)))) (orderedInterval (-6556168920 / 1000000000000) (-6556168834 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks2 :
    compactCertificate269.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate269.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate269_chunkChecks2_0
    compactCertificate269_chunkChecks2_1 compactCertificate269_chunkChecks2_2

theorem compactCertificate269_chunkChecks3_0 :
    compactCertificate269.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (287 / 2) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15102598980 / 1000000000000) (-15102598836 / 1000000000000), orderedInterval (64924112896 / 1000000000000) (64924113041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (422805802047587 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25036464349 / 1000000000000) (-25036463675 / 1000000000000), orderedInterval (73576163231 / 1000000000000) (73576163905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (136726709288771 / 800000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54240247127 / 1000000000000) (54240262772 / 1000000000000), orderedInterval (-28139105487 / 1000000000000) (-28139089843 / 1000000000000)))) (orderedInterval (-23226815821 / 1000000000000) (-23226814185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (123373678544809 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (29784069155 / 1000000000000) (29784069156 / 1000000000000), orderedInterval (140072484110 / 1000000000000) (140072484111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (331399054514773 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81357518783 / 1000000000000) (81357522602 / 1000000000000), orderedInterval (-33123463601 / 1000000000000) (-33123459782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (899812899304641 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23455020181 / 1000000000000) (-23455018664 / 1000000000000), orderedInterval (47800177838 / 1000000000000) (47800179355 / 1000000000000)))) (orderedInterval (13373088597 / 1000000000000) (13373089083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (662798109029833 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1254441284 / 1000000000000) (1254441290 / 1000000000000), orderedInterval (-61975206588 / 1000000000000) (-61975206582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1135715856854509 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (43617653929 / 1000000000000) (43617666885 / 1000000000000), orderedInterval (-18507145225 / 1000000000000) (-18507132270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (836563159852231 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29358904368 / 1000000000000) (29358909588 / 1000000000000), orderedInterval (-46782453585 / 1000000000000) (-46782448364 / 1000000000000)))) (orderedInterval (-947757756 / 1000000000000) (-947754212 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks3_1 :
    compactCertificate269.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1283503019084713 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (41803634385 / 1000000000000) (41803634387 / 1000000000000), orderedInterval (15312161940 / 1000000000000) (15312161942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (741030813574177 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37244609642 / 1000000000000) (-37244609641 / 1000000000000), orderedInterval (-45168039886 / 1000000000000) (-45168039885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1314972182535893 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14640776377 / 1000000000000) (14640776559 / 1000000000000), orderedInterval (-41521380769 / 1000000000000) (-41521380587 / 1000000000000)))) (orderedInterval (108368993662 / 1000000000000) (108368994532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1228617586630217 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2880239199 / 1000000000000) (2880239201 / 1000000000000), orderedInterval (45430370732 / 1000000000000) (45430370734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (876799482967961 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3942021037 / 1000000000000) (3942021038 / 1000000000000), orderedInterval (53738165710 / 1000000000000) (53738165712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000)))) (orderedInterval (-10602476257 / 1000000000000) (-10602476178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (828857944698511 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33727818006 / 1000000000000) (33727818007 / 1000000000000), orderedInterval (43903967236 / 1000000000000) (43903967237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (732321130880731 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58770970543 / 1000000000000) (58770970734 / 1000000000000), orderedInterval (-4980390339 / 1000000000000) (-4980390148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (212255207316369 / 800000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39308720941 / 1000000000000) (39308824167 / 1000000000000), orderedInterval (-29302013876 / 1000000000000) (-29301910650 / 1000000000000)))) (orderedInterval (2614959410 / 1000000000000) (2614976247 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks3_2 :
    compactCertificate269.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (587109073816643 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6118585066 / 1000000000000) (6118585085 / 1000000000000), orderedInterval (-65594513021 / 1000000000000) (-65594513002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (497698863929323 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31408582958 / 1000000000000) (-31408580335 / 1000000000000), orderedInterval (64391537622 / 1000000000000) (64391540245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (311436840147769 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9313923389 / 1000000000000) (-9313923387 / 1000000000000), orderedInterval (-89884430570 / 1000000000000) (-89884430568 / 1000000000000)))) (orderedInterval (-8377858967 / 1000000000000) (-8377858834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (167491768423623 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-119650656347 / 1000000000000) (-119650655718 / 1000000000000), orderedInterval (31200519589 / 1000000000000) (31200520218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (454772733059869 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (73473332435 / 1000000000000) (73473332438 / 1000000000000), orderedInterval (13856919210 / 1000000000000) (13856919212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (620953287276413 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55761077737 / 1000000000000) (-55761056925 / 1000000000000), orderedInterval (31669445229 / 1000000000000) (31669466042 / 1000000000000)))) (orderedInterval (3272010360 / 1000000000000) (3272012409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (262563159852231 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42909614168 / 1000000000000) (-42909614167 / 1000000000000), orderedInterval (-88315587326 / 1000000000000) (-88315587325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1067304667728551 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26593488582 / 1000000000000) (-26593488581 / 1000000000000), orderedInterval (-40921927587 / 1000000000000) (-40921927586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (712910054807209 / 4000000000000) 3 (IntervalRat.scale (287 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3498518064 / 1000000000000) (3498518073 / 1000000000000), orderedInterval (-59673240306 / 1000000000000) (-59673240297 / 1000000000000)))) (orderedInterval (-42768208772 / 1000000000000) (-42768208641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks3 :
    compactCertificate269.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate269.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate269_chunkChecks3_0
    compactCertificate269_chunkChecks3_1 compactCertificate269_chunkChecks3_2

theorem compactCertificate269_chunkChecks4_0 :
    compactCertificate269.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (287 / 2) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15102598980 / 1000000000000) (-15102598836 / 1000000000000), orderedInterval (64924112896 / 1000000000000) (64924113041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (422805802047587 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25036464349 / 1000000000000) (-25036463675 / 1000000000000), orderedInterval (73576163231 / 1000000000000) (73576163905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (136726709288771 / 800000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54240247127 / 1000000000000) (54240262772 / 1000000000000), orderedInterval (-28139105487 / 1000000000000) (-28139089843 / 1000000000000)))) (orderedInterval (673178580 / 1000000000000) (673180527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (123373678544809 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (29784069155 / 1000000000000) (29784069156 / 1000000000000), orderedInterval (140072484110 / 1000000000000) (140072484111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (331399054514773 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81357518783 / 1000000000000) (81357522602 / 1000000000000), orderedInterval (-33123463601 / 1000000000000) (-33123459782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (899812899304641 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23455020181 / 1000000000000) (-23455018664 / 1000000000000), orderedInterval (47800177838 / 1000000000000) (47800179355 / 1000000000000)))) (orderedInterval (10212135238 / 1000000000000) (10212135975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (662798109029833 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1254441284 / 1000000000000) (1254441290 / 1000000000000), orderedInterval (-61975206588 / 1000000000000) (-61975206582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1135715856854509 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (43617653929 / 1000000000000) (43617666885 / 1000000000000), orderedInterval (-18507145225 / 1000000000000) (-18507132270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (836563159852231 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29358904368 / 1000000000000) (29358909588 / 1000000000000), orderedInterval (-46782453585 / 1000000000000) (-46782448364 / 1000000000000)))) (orderedInterval (-17404137690 / 1000000000000) (-17404130863 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks4_1 :
    compactCertificate269.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1283503019084713 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (41803634385 / 1000000000000) (41803634387 / 1000000000000), orderedInterval (15312161940 / 1000000000000) (15312161942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (741030813574177 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37244609642 / 1000000000000) (-37244609641 / 1000000000000), orderedInterval (-45168039886 / 1000000000000) (-45168039885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1314972182535893 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14640776377 / 1000000000000) (14640776559 / 1000000000000), orderedInterval (-41521380769 / 1000000000000) (-41521380587 / 1000000000000)))) (orderedInterval (-137548739895 / 1000000000000) (-137548737938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1228617586630217 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2880239199 / 1000000000000) (2880239201 / 1000000000000), orderedInterval (45430370732 / 1000000000000) (45430370734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (876799482967961 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3942021037 / 1000000000000) (3942021038 / 1000000000000), orderedInterval (53738165710 / 1000000000000) (53738165712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (994197163544319 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-46160834514 / 1000000000000) (-46160834513 / 1000000000000), orderedInterval (-20656020682 / 1000000000000) (-20656020681 / 1000000000000)))) (orderedInterval (3188184807 / 1000000000000) (3188184945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (828857944698511 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33727818006 / 1000000000000) (33727818007 / 1000000000000), orderedInterval (43903967236 / 1000000000000) (43903967237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (732321130880731 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (58770970543 / 1000000000000) (58770970734 / 1000000000000), orderedInterval (-4980390339 / 1000000000000) (-4980390148 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (212255207316369 / 800000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39308720941 / 1000000000000) (39308824167 / 1000000000000), orderedInterval (-29302013876 / 1000000000000) (-29301910650 / 1000000000000)))) (orderedInterval (4507602116 / 1000000000000) (4507633336 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks4_2 :
    compactCertificate269.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (587109073816643 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6118585066 / 1000000000000) (6118585085 / 1000000000000), orderedInterval (-65594513021 / 1000000000000) (-65594513002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (497698863929323 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31408582958 / 1000000000000) (-31408580335 / 1000000000000), orderedInterval (64391537622 / 1000000000000) (64391540245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (311436840147769 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9313923389 / 1000000000000) (-9313923387 / 1000000000000), orderedInterval (-89884430570 / 1000000000000) (-89884430568 / 1000000000000)))) (orderedInterval (24485307 / 1000000000000) (24485427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (167491768423623 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-119650656347 / 1000000000000) (-119650655718 / 1000000000000), orderedInterval (31200519589 / 1000000000000) (31200520218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (454772733059869 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (73473332435 / 1000000000000) (73473332438 / 1000000000000), orderedInterval (13856919210 / 1000000000000) (13856919212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (620953287276413 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55761077737 / 1000000000000) (-55761056925 / 1000000000000), orderedInterval (31669445229 / 1000000000000) (31669466042 / 1000000000000)))) (orderedInterval (5166275084 / 1000000000000) (5166277314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (262563159852231 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42909614168 / 1000000000000) (-42909614167 / 1000000000000), orderedInterval (-88315587326 / 1000000000000) (-88315587325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1067304667728551 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26593488582 / 1000000000000) (-26593488581 / 1000000000000), orderedInterval (-40921927587 / 1000000000000) (-40921927586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (712910054807209 / 4000000000000) 4 (IntervalRat.scale (287 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3498518064 / 1000000000000) (3498518073 / 1000000000000), orderedInterval (-59673240306 / 1000000000000) (-59673240297 / 1000000000000)))) (orderedInterval (24899542647 / 1000000000000) (24899542857 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate269_chunkChecks4 :
    compactCertificate269.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate269.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate269_chunkChecks4_0
    compactCertificate269_chunkChecks4_1 compactCertificate269_chunkChecks4_2

theorem compactCertificate269_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate269.chunkCheck r b = true :=
  compactCertificate269.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate269_chunkChecks0
    · exact compactCertificate269_chunkChecks1
    · exact compactCertificate269_chunkChecks2
    · exact compactCertificate269_chunkChecks3
    · exact compactCertificate269_chunkChecks4)

theorem compactCertificate269_coefficient0 :
    compactCertificate269.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate269, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate269_coefficient1 :
    compactCertificate269.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate269, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate269_coefficient2 :
    compactCertificate269.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate269, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate269_coefficient3 :
    compactCertificate269.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate269, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate269_coefficient4 :
    compactCertificate269.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate269, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate269_coefficients : ∀ r : Fin 5,
    compactCertificate269.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate269_coefficient0
  · exact compactCertificate269_coefficient1
  · exact compactCertificate269_coefficient2
  · exact compactCertificate269_coefficient3
  · exact compactCertificate269_coefficient4

theorem compactCertificate269_lower : (1 : ℚ) ≤ compactCertificate269.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate269, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate269_proves {t : ℝ} (ht : t ∈ compactCertificate269.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate269.proves compactCertificate269_states compactCertificate269_chunks
    compactCertificate269_coefficients compactCertificate269_lower ht

end Erdos232
