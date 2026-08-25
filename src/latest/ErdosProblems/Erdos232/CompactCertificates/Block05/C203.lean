/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate203 : CompactCertificate where
  left := 739 / 8
  right := 2957 / 32
  center := 5913 / 64
  grid := fun i =>
    match i.val with
    | 0 => 29
    | 1 => 22
    | 2 => 35
    | 3 => 6
    | 4 => 17
    | 5 => 46
    | 6 => 34
    | 7 => 58
    | 8 => 43
    | 9 => 66
    | 10 => 38
    | 11 => 67
    | 12 => 63
    | 13 => 45
    | 14 => 51
    | 15 => 42
    | 16 => 38
    | 17 => 54
    | 18 => 30
    | 19 => 26
    | 20 => 16
    | 21 => 9
    | 22 => 23
    | 23 => 32
    | 24 => 13
    | 25 => 55
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 5913 / 64
    | 1 => 8710978074938613 / 128000000000000
    | 2 => 2816951331095829 / 25600000000000
    | 3 => 2541841676778591 / 128000000000000
    | 4 => 6827744283435027 / 128000000000000
    | 5 => 18538653914941959 / 128000000000000
    | 6 => 13655488566875967 / 128000000000000
    | 7 => 23398912409688891 / 128000000000000
    | 8 => 17235532976328369 / 128000000000000
    | 9 => 26443739901909087 / 128000000000000
    | 10 => 15267300350746023 / 128000000000000
    | 11 => 27092092387925907 / 128000000000000
    | 12 => 25312947002593983 / 128000000000000
    | 13 => 18064513389510639 / 128000000000000
    | 14 => 20483232850305081 / 128000000000000
    | 15 => 17076784066210089 / 128000000000000
    | 16 => 15087856609399869 / 128000000000000
    | 17 => 4373048922863031 / 25600000000000
    | 18 => 12096083461595157 / 128000000000000
    | 19 => 10253983910850477 / 128000000000000
    | 20 => 6416467023671631 / 128000000000000
    | 21 => 3450797305536177 / 128000000000000
    | 22 => 9369585960219531 / 128000000000000
    | 23 => 12793368598137387 / 128000000000000
    | 24 => 5409532976328369 / 128000000000000
    | 25 => 21989451220484049 / 128000000000000
    | _ => 14687934334756191 / 128000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-72938732978 / 1000000000000) (-72938719811 / 1000000000000), orderedInterval (40023119794 / 1000000000000) (40023132961 / 1000000000000))
    | 1 => (orderedInterval (-26445826642 / 1000000000000) (-26445826195 / 1000000000000), orderedInterval (93228629945 / 1000000000000) (93228630391 / 1000000000000))
    | 2 => (orderedInterval (-57924051532 / 1000000000000) (-57924051531 / 1000000000000), orderedInterval (-49034801792 / 1000000000000) (-49034801791 / 1000000000000))
    | 3 => (orderedInterval (174825801902 / 1000000000000) (174825802309 / 1000000000000), orderedInterval (-42936602671 / 1000000000000) (-42936602265 / 1000000000000))
    | 4 => (orderedInterval (-71847271846 / 1000000000000) (-71847271845 / 1000000000000), orderedInterval (-81623480685 / 1000000000000) (-81623480684 / 1000000000000))
    | 5 => (orderedInterval (59220771271 / 1000000000000) (59220771272 / 1000000000000), orderedInterval (29601952965 / 1000000000000) (29601952966 / 1000000000000))
    | 6 => (orderedInterval (46969533926 / 1000000000000) (46969533927 / 1000000000000), orderedInterval (61108887106 / 1000000000000) (61108887107 / 1000000000000))
    | 7 => (orderedInterval (57900643592 / 1000000000000) (57900643595 / 1000000000000), orderedInterval (11244696124 / 1000000000000) (11244696127 / 1000000000000))
    | 8 => (orderedInterval (-23486118916 / 1000000000000) (-23486118915 / 1000000000000), orderedInterval (-64537055607 / 1000000000000) (-64537055606 / 1000000000000))
    | 9 => (orderedInterval (1742550528 / 1000000000000) (1742550530 / 1000000000000), orderedInterval (55480089546 / 1000000000000) (55480089548 / 1000000000000))
    | 10 => (orderedInterval (45915783817 / 1000000000000) (45915783818 / 1000000000000), orderedInterval (56632935733 / 1000000000000) (56632935734 / 1000000000000))
    | 11 => (orderedInterval (-50843554036 / 1000000000000) (-50843546324 / 1000000000000), orderedInterval (20680200716 / 1000000000000) (20680208428 / 1000000000000))
    | 12 => (orderedInterval (-33051023597 / 1000000000000) (-33051023596 / 1000000000000), orderedInterval (-46033990908 / 1000000000000) (-46033990907 / 1000000000000))
    | 13 => (orderedInterval (-34637690379 / 1000000000000) (-34637690378 / 1000000000000), orderedInterval (-57419879397 / 1000000000000) (-57419879396 / 1000000000000))
    | 14 => (orderedInterval (-35020588120 / 1000000000000) (-35020588119 / 1000000000000), orderedInterval (-52348290050 / 1000000000000) (-52348290049 / 1000000000000))
    | 15 => (orderedInterval (53750159659 / 1000000000000) (53750242168 / 1000000000000), orderedInterval (-43591895134 / 1000000000000) (-43591812625 / 1000000000000))
    | 16 => (orderedInterval (-48585448423 / 1000000000000) (-48585409570 / 1000000000000), orderedInterval (55345140272 / 1000000000000) (55345179124 / 1000000000000))
    | 17 => (orderedInterval (56461163274 / 1000000000000) (56461169905 / 1000000000000), orderedInterval (-23379967677 / 1000000000000) (-23379961046 / 1000000000000))
    | 18 => (orderedInterval (70656110232 / 1000000000000) (70656110233 / 1000000000000), orderedInterval (41391459618 / 1000000000000) (41391459619 / 1000000000000))
    | 19 => (orderedInterval (-63218729848 / 1000000000000) (-63218648469 / 1000000000000), orderedInterval (63245858819 / 1000000000000) (63245940198 / 1000000000000))
    | 20 => (orderedInterval (67845619680 / 1000000000000) (67845619681 / 1000000000000), orderedInterval (89305933734 / 1000000000000) (89305933735 / 1000000000000))
    | 21 => (orderedInterval (78236085126 / 1000000000000) (78236094918 / 1000000000000), orderedInterval (-133719645172 / 1000000000000) (-133719635380 / 1000000000000))
    | 22 => (orderedInterval (-92121969512 / 1000000000000) (-92121969265 / 1000000000000), orderedInterval (15132812497 / 1000000000000) (15132812745 / 1000000000000))
    | 23 => (orderedInterval (15963049556 / 1000000000000) (15963049557 / 1000000000000), orderedInterval (78117025005 / 1000000000000) (78117025007 / 1000000000000))
    | 24 => (orderedInterval (-98957735372 / 1000000000000) (-98957697942 / 1000000000000), orderedInterval (73770219245 / 1000000000000) (73770256675 / 1000000000000))
    | 25 => (orderedInterval (12710043648 / 1000000000000) (12710043740 / 1000000000000), orderedInterval (-59570306920 / 1000000000000) (-59570306828 / 1000000000000))
    | _ => (orderedInterval (48275598641 / 1000000000000) (48275632382 / 1000000000000), orderedInterval (-56932342417 / 1000000000000) (-56932308676 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-32555833567 / 1000000000000) (-32555828336 / 1000000000000)
      | 1 => orderedInterval (-8729988719 / 1000000000000) (-8729988703 / 1000000000000)
      | 2 => orderedInterval (-2353500668 / 1000000000000) (-2353500662 / 1000000000000)
      | 3 => orderedInterval (-4135359245 / 1000000000000) (-4135358111 / 1000000000000)
      | 4 => orderedInterval (-2501541961 / 1000000000000) (-2501541949 / 1000000000000)
      | 5 => orderedInterval (4846699443 / 1000000000000) (4846702799 / 1000000000000)
      | 6 => orderedInterval (-5510472763 / 1000000000000) (-5510468133 / 1000000000000)
      | 7 => orderedInterval (-578070328 / 1000000000000) (-578070130 / 1000000000000)
      | _ => orderedInterval (-10688959089 / 1000000000000) (-10688952499 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13076648777 / 1000000000000) (13076654007 / 1000000000000)
      | 1 => orderedInterval (-4919387780 / 1000000000000) (-4919387766 / 1000000000000)
      | 2 => orderedInterval (-2959437917 / 1000000000000) (-2959437907 / 1000000000000)
      | 3 => orderedInterval (-9891624976 / 1000000000000) (-9891622387 / 1000000000000)
      | 4 => orderedInterval (-6056464904 / 1000000000000) (-6056464885 / 1000000000000)
      | 5 => orderedInterval (-5874490772 / 1000000000000) (-5874486232 / 1000000000000)
      | 6 => orderedInterval (-8295733205 / 1000000000000) (-8295729189 / 1000000000000)
      | 7 => orderedInterval (-6028035115 / 1000000000000) (-6028035047 / 1000000000000)
      | _ => orderedInterval (22487065976 / 1000000000000) (22487073992 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (33724002006 / 1000000000000) (33724007293 / 1000000000000)
      | 1 => orderedInterval (11361020909 / 1000000000000) (11361020928 / 1000000000000)
      | 2 => orderedInterval (8229184604 / 1000000000000) (8229184621 / 1000000000000)
      | 3 => orderedInterval (33917620301 / 1000000000000) (33917626248 / 1000000000000)
      | 4 => orderedInterval (4442901710 / 1000000000000) (4442901741 / 1000000000000)
      | 5 => orderedInterval (-10698181159 / 1000000000000) (-10698174904 / 1000000000000)
      | 6 => orderedInterval (8568744921 / 1000000000000) (8568748448 / 1000000000000)
      | 7 => orderedInterval (308067133 / 1000000000000) (308067164 / 1000000000000)
      | _ => orderedInterval (17430844520 / 1000000000000) (17430854499 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11713306455 / 1000000000000) (-11713301168 / 1000000000000)
      | 1 => orderedInterval (8552139981 / 1000000000000) (8552140008 / 1000000000000)
      | 2 => orderedInterval (7425599466 / 1000000000000) (7425599496 / 1000000000000)
      | 3 => orderedInterval (65475207000 / 1000000000000) (65475220605 / 1000000000000)
      | 4 => orderedInterval (9777911267 / 1000000000000) (9777911319 / 1000000000000)
      | 5 => orderedInterval (11991618738 / 1000000000000) (11991627393 / 1000000000000)
      | 6 => orderedInterval (8857482135 / 1000000000000) (8857485195 / 1000000000000)
      | 7 => orderedInterval (7684773866 / 1000000000000) (7684773884 / 1000000000000)
      | _ => orderedInterval (-51868123075 / 1000000000000) (-51868110689 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-35564578853 / 1000000000000) (-35564573509 / 1000000000000)
      | 1 => orderedInterval (-25903185933 / 1000000000000) (-25903185891 / 1000000000000)
      | 2 => orderedInterval (-30091379413 / 1000000000000) (-30091379357 / 1000000000000)
      | 3 => orderedInterval (-198780429573 / 1000000000000) (-198780398292 / 1000000000000)
      | 4 => orderedInterval (-3924699766 / 1000000000000) (-3924699677 / 1000000000000)
      | 5 => orderedInterval (26697970892 / 1000000000000) (26697983140 / 1000000000000)
      | 6 => orderedInterval (-10342166150 / 1000000000000) (-10342163462 / 1000000000000)
      | 7 => orderedInterval (-1028809213 / 1000000000000) (-1028809198 / 1000000000000)
      | _ => orderedInterval (-32822239939 / 1000000000000) (-32822224382 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-62207026897 / 1000000000000) (-62207005724 / 1000000000000)
    | 1 => orderedInterval (-8461459916 / 1000000000000) (-8461435414 / 1000000000000)
    | 2 => orderedInterval (107284204945 / 1000000000000) (107284236038 / 1000000000000)
    | 3 => orderedInterval (56183302923 / 1000000000000) (56183346043 / 1000000000000)
    | _ => orderedInterval (-311759517948 / 1000000000000) (-311759450628 / 1000000000000)

theorem compactCertificate203_stateChecks0 :
    compactCertificate203.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (5913 / 64)) (orderedInterval (-72938732978 / 1000000000000) (-72938719811 / 1000000000000), orderedInterval (40023119794 / 1000000000000) (40023132961 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (8710978074938613 / 128000000000000)) (orderedInterval (-26445826642 / 1000000000000) (-26445826195 / 1000000000000), orderedInterval (93228629945 / 1000000000000) (93228630391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (2816951331095829 / 25600000000000)) (orderedInterval (-57924051532 / 1000000000000) (-57924051531 / 1000000000000), orderedInterval (-49034801792 / 1000000000000) (-49034801791 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_stateChecks1 :
    compactCertificate203.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (2541841676778591 / 128000000000000)) (orderedInterval (174825801902 / 1000000000000) (174825802309 / 1000000000000), orderedInterval (-42936602671 / 1000000000000) (-42936602265 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (6827744283435027 / 128000000000000)) (orderedInterval (-71847271846 / 1000000000000) (-71847271845 / 1000000000000), orderedInterval (-81623480685 / 1000000000000) (-81623480684 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (18538653914941959 / 128000000000000)) (orderedInterval (59220771271 / 1000000000000) (59220771272 / 1000000000000), orderedInterval (29601952965 / 1000000000000) (29601952966 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_stateChecks2 :
    compactCertificate203.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (13655488566875967 / 128000000000000)) (orderedInterval (46969533926 / 1000000000000) (46969533927 / 1000000000000), orderedInterval (61108887106 / 1000000000000) (61108887107 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (23398912409688891 / 128000000000000)) (orderedInterval (57900643592 / 1000000000000) (57900643595 / 1000000000000), orderedInterval (11244696124 / 1000000000000) (11244696127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17235532976328369 / 128000000000000)) (orderedInterval (-23486118916 / 1000000000000) (-23486118915 / 1000000000000), orderedInterval (-64537055607 / 1000000000000) (-64537055606 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_stateChecks3 :
    compactCertificate203.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (26443739901909087 / 128000000000000)) (orderedInterval (1742550528 / 1000000000000) (1742550530 / 1000000000000), orderedInterval (55480089546 / 1000000000000) (55480089548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15267300350746023 / 128000000000000)) (orderedInterval (45915783817 / 1000000000000) (45915783818 / 1000000000000), orderedInterval (56632935733 / 1000000000000) (56632935734 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (27092092387925907 / 128000000000000)) (orderedInterval (-50843554036 / 1000000000000) (-50843546324 / 1000000000000), orderedInterval (20680200716 / 1000000000000) (20680208428 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_stateChecks4 :
    compactCertificate203.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (25312947002593983 / 128000000000000)) (orderedInterval (-33051023597 / 1000000000000) (-33051023596 / 1000000000000), orderedInterval (-46033990908 / 1000000000000) (-46033990907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (18064513389510639 / 128000000000000)) (orderedInterval (-34637690379 / 1000000000000) (-34637690378 / 1000000000000), orderedInterval (-57419879397 / 1000000000000) (-57419879396 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (20483232850305081 / 128000000000000)) (orderedInterval (-35020588120 / 1000000000000) (-35020588119 / 1000000000000), orderedInterval (-52348290050 / 1000000000000) (-52348290049 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_stateChecks5 :
    compactCertificate203.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (17076784066210089 / 128000000000000)) (orderedInterval (53750159659 / 1000000000000) (53750242168 / 1000000000000), orderedInterval (-43591895134 / 1000000000000) (-43591812625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15087856609399869 / 128000000000000)) (orderedInterval (-48585448423 / 1000000000000) (-48585409570 / 1000000000000), orderedInterval (55345140272 / 1000000000000) (55345179124 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (4373048922863031 / 25600000000000)) (orderedInterval (56461163274 / 1000000000000) (56461169905 / 1000000000000), orderedInterval (-23379967677 / 1000000000000) (-23379961046 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_stateChecks6 :
    compactCertificate203.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (12096083461595157 / 128000000000000)) (orderedInterval (70656110232 / 1000000000000) (70656110233 / 1000000000000), orderedInterval (41391459618 / 1000000000000) (41391459619 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (10253983910850477 / 128000000000000)) (orderedInterval (-63218729848 / 1000000000000) (-63218648469 / 1000000000000), orderedInterval (63245858819 / 1000000000000) (63245940198 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (6416467023671631 / 128000000000000)) (orderedInterval (67845619680 / 1000000000000) (67845619681 / 1000000000000), orderedInterval (89305933734 / 1000000000000) (89305933735 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_stateChecks7 :
    compactCertificate203.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (3450797305536177 / 128000000000000)) (orderedInterval (78236085126 / 1000000000000) (78236094918 / 1000000000000), orderedInterval (-133719645172 / 1000000000000) (-133719635380 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (9369585960219531 / 128000000000000)) (orderedInterval (-92121969512 / 1000000000000) (-92121969265 / 1000000000000), orderedInterval (15132812497 / 1000000000000) (15132812745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (12793368598137387 / 128000000000000)) (orderedInterval (15963049556 / 1000000000000) (15963049557 / 1000000000000), orderedInterval (78117025005 / 1000000000000) (78117025007 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_stateChecks8 :
    compactCertificate203.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (5409532976328369 / 128000000000000)) (orderedInterval (-98957735372 / 1000000000000) (-98957697942 / 1000000000000), orderedInterval (73770219245 / 1000000000000) (73770256675 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (21989451220484049 / 128000000000000)) (orderedInterval (12710043648 / 1000000000000) (12710043740 / 1000000000000), orderedInterval (-59570306920 / 1000000000000) (-59570306828 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (14687934334756191 / 128000000000000)) (orderedInterval (48275598641 / 1000000000000) (48275632382 / 1000000000000), orderedInterval (-56932342417 / 1000000000000) (-56932308676 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate203_states : ∀ j,
    BesselStateValid (compactCertificate203.point j) (compactCertificate203.state j) :=
  compactCertificate203.statesValid_of_checks3 compactCertificate203_stateChecks0
    compactCertificate203_stateChecks1 compactCertificate203_stateChecks2
    compactCertificate203_stateChecks3 compactCertificate203_stateChecks4
    compactCertificate203_stateChecks5 compactCertificate203_stateChecks6
    compactCertificate203_stateChecks7 compactCertificate203_stateChecks8

theorem compactCertificate203_chunkChecks0_0 :
    compactCertificate203.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (5913 / 64) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-72938732978 / 1000000000000) (-72938719811 / 1000000000000), orderedInterval (40023119794 / 1000000000000) (40023132961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (8710978074938613 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26445826642 / 1000000000000) (-26445826195 / 1000000000000), orderedInterval (93228629945 / 1000000000000) (93228630391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (2816951331095829 / 25600000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57924051532 / 1000000000000) (-57924051531 / 1000000000000), orderedInterval (-49034801792 / 1000000000000) (-49034801791 / 1000000000000)))) (orderedInterval (-32555833567 / 1000000000000) (-32555828336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (2541841676778591 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174825801902 / 1000000000000) (174825802309 / 1000000000000), orderedInterval (-42936602671 / 1000000000000) (-42936602265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (6827744283435027 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71847271846 / 1000000000000) (-71847271845 / 1000000000000), orderedInterval (-81623480685 / 1000000000000) (-81623480684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (18538653914941959 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (59220771271 / 1000000000000) (59220771272 / 1000000000000), orderedInterval (29601952965 / 1000000000000) (29601952966 / 1000000000000)))) (orderedInterval (-8729988719 / 1000000000000) (-8729988703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (13655488566875967 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46969533926 / 1000000000000) (46969533927 / 1000000000000), orderedInterval (61108887106 / 1000000000000) (61108887107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (23398912409688891 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57900643592 / 1000000000000) (57900643595 / 1000000000000), orderedInterval (11244696124 / 1000000000000) (11244696127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (17235532976328369 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23486118916 / 1000000000000) (-23486118915 / 1000000000000), orderedInterval (-64537055607 / 1000000000000) (-64537055606 / 1000000000000)))) (orderedInterval (-2353500668 / 1000000000000) (-2353500662 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks0_1 :
    compactCertificate203.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (26443739901909087 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1742550528 / 1000000000000) (1742550530 / 1000000000000), orderedInterval (55480089546 / 1000000000000) (55480089548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (15267300350746023 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45915783817 / 1000000000000) (45915783818 / 1000000000000), orderedInterval (56632935733 / 1000000000000) (56632935734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (27092092387925907 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-50843554036 / 1000000000000) (-50843546324 / 1000000000000), orderedInterval (20680200716 / 1000000000000) (20680208428 / 1000000000000)))) (orderedInterval (-4135359245 / 1000000000000) (-4135358111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (25312947002593983 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33051023597 / 1000000000000) (-33051023596 / 1000000000000), orderedInterval (-46033990908 / 1000000000000) (-46033990907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (18064513389510639 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34637690379 / 1000000000000) (-34637690378 / 1000000000000), orderedInterval (-57419879397 / 1000000000000) (-57419879396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (20483232850305081 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35020588120 / 1000000000000) (-35020588119 / 1000000000000), orderedInterval (-52348290050 / 1000000000000) (-52348290049 / 1000000000000)))) (orderedInterval (-2501541961 / 1000000000000) (-2501541949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (17076784066210089 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (53750159659 / 1000000000000) (53750242168 / 1000000000000), orderedInterval (-43591895134 / 1000000000000) (-43591812625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (15087856609399869 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-48585448423 / 1000000000000) (-48585409570 / 1000000000000), orderedInterval (55345140272 / 1000000000000) (55345179124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (4373048922863031 / 25600000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56461163274 / 1000000000000) (56461169905 / 1000000000000), orderedInterval (-23379967677 / 1000000000000) (-23379961046 / 1000000000000)))) (orderedInterval (4846699443 / 1000000000000) (4846702799 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks0_2 :
    compactCertificate203.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (12096083461595157 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70656110232 / 1000000000000) (70656110233 / 1000000000000), orderedInterval (41391459618 / 1000000000000) (41391459619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (10253983910850477 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63218729848 / 1000000000000) (-63218648469 / 1000000000000), orderedInterval (63245858819 / 1000000000000) (63245940198 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (6416467023671631 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67845619680 / 1000000000000) (67845619681 / 1000000000000), orderedInterval (89305933734 / 1000000000000) (89305933735 / 1000000000000)))) (orderedInterval (-5510472763 / 1000000000000) (-5510468133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (3450797305536177 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78236085126 / 1000000000000) (78236094918 / 1000000000000), orderedInterval (-133719645172 / 1000000000000) (-133719635380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (9369585960219531 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92121969512 / 1000000000000) (-92121969265 / 1000000000000), orderedInterval (15132812497 / 1000000000000) (15132812745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (12793368598137387 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15963049556 / 1000000000000) (15963049557 / 1000000000000), orderedInterval (78117025005 / 1000000000000) (78117025007 / 1000000000000)))) (orderedInterval (-578070328 / 1000000000000) (-578070130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (5409532976328369 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-98957735372 / 1000000000000) (-98957697942 / 1000000000000), orderedInterval (73770219245 / 1000000000000) (73770256675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (21989451220484049 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12710043648 / 1000000000000) (12710043740 / 1000000000000), orderedInterval (-59570306920 / 1000000000000) (-59570306828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (14687934334756191 / 128000000000000) 0 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48275598641 / 1000000000000) (48275632382 / 1000000000000), orderedInterval (-56932342417 / 1000000000000) (-56932308676 / 1000000000000)))) (orderedInterval (-10688959089 / 1000000000000) (-10688952499 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks0 :
    compactCertificate203.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate203.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate203_chunkChecks0_0
    compactCertificate203_chunkChecks0_1 compactCertificate203_chunkChecks0_2

theorem compactCertificate203_chunkChecks1_0 :
    compactCertificate203.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (5913 / 64) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-72938732978 / 1000000000000) (-72938719811 / 1000000000000), orderedInterval (40023119794 / 1000000000000) (40023132961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (8710978074938613 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26445826642 / 1000000000000) (-26445826195 / 1000000000000), orderedInterval (93228629945 / 1000000000000) (93228630391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (2816951331095829 / 25600000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57924051532 / 1000000000000) (-57924051531 / 1000000000000), orderedInterval (-49034801792 / 1000000000000) (-49034801791 / 1000000000000)))) (orderedInterval (13076648777 / 1000000000000) (13076654007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (2541841676778591 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174825801902 / 1000000000000) (174825802309 / 1000000000000), orderedInterval (-42936602671 / 1000000000000) (-42936602265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (6827744283435027 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71847271846 / 1000000000000) (-71847271845 / 1000000000000), orderedInterval (-81623480685 / 1000000000000) (-81623480684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (18538653914941959 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (59220771271 / 1000000000000) (59220771272 / 1000000000000), orderedInterval (29601952965 / 1000000000000) (29601952966 / 1000000000000)))) (orderedInterval (-4919387780 / 1000000000000) (-4919387766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (13655488566875967 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46969533926 / 1000000000000) (46969533927 / 1000000000000), orderedInterval (61108887106 / 1000000000000) (61108887107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (23398912409688891 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57900643592 / 1000000000000) (57900643595 / 1000000000000), orderedInterval (11244696124 / 1000000000000) (11244696127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (17235532976328369 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23486118916 / 1000000000000) (-23486118915 / 1000000000000), orderedInterval (-64537055607 / 1000000000000) (-64537055606 / 1000000000000)))) (orderedInterval (-2959437917 / 1000000000000) (-2959437907 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks1_1 :
    compactCertificate203.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (26443739901909087 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1742550528 / 1000000000000) (1742550530 / 1000000000000), orderedInterval (55480089546 / 1000000000000) (55480089548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (15267300350746023 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45915783817 / 1000000000000) (45915783818 / 1000000000000), orderedInterval (56632935733 / 1000000000000) (56632935734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (27092092387925907 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-50843554036 / 1000000000000) (-50843546324 / 1000000000000), orderedInterval (20680200716 / 1000000000000) (20680208428 / 1000000000000)))) (orderedInterval (-9891624976 / 1000000000000) (-9891622387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (25312947002593983 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33051023597 / 1000000000000) (-33051023596 / 1000000000000), orderedInterval (-46033990908 / 1000000000000) (-46033990907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (18064513389510639 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34637690379 / 1000000000000) (-34637690378 / 1000000000000), orderedInterval (-57419879397 / 1000000000000) (-57419879396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (20483232850305081 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35020588120 / 1000000000000) (-35020588119 / 1000000000000), orderedInterval (-52348290050 / 1000000000000) (-52348290049 / 1000000000000)))) (orderedInterval (-6056464904 / 1000000000000) (-6056464885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (17076784066210089 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (53750159659 / 1000000000000) (53750242168 / 1000000000000), orderedInterval (-43591895134 / 1000000000000) (-43591812625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (15087856609399869 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-48585448423 / 1000000000000) (-48585409570 / 1000000000000), orderedInterval (55345140272 / 1000000000000) (55345179124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (4373048922863031 / 25600000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56461163274 / 1000000000000) (56461169905 / 1000000000000), orderedInterval (-23379967677 / 1000000000000) (-23379961046 / 1000000000000)))) (orderedInterval (-5874490772 / 1000000000000) (-5874486232 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks1_2 :
    compactCertificate203.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (12096083461595157 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70656110232 / 1000000000000) (70656110233 / 1000000000000), orderedInterval (41391459618 / 1000000000000) (41391459619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (10253983910850477 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63218729848 / 1000000000000) (-63218648469 / 1000000000000), orderedInterval (63245858819 / 1000000000000) (63245940198 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (6416467023671631 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67845619680 / 1000000000000) (67845619681 / 1000000000000), orderedInterval (89305933734 / 1000000000000) (89305933735 / 1000000000000)))) (orderedInterval (-8295733205 / 1000000000000) (-8295729189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (3450797305536177 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78236085126 / 1000000000000) (78236094918 / 1000000000000), orderedInterval (-133719645172 / 1000000000000) (-133719635380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (9369585960219531 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92121969512 / 1000000000000) (-92121969265 / 1000000000000), orderedInterval (15132812497 / 1000000000000) (15132812745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (12793368598137387 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15963049556 / 1000000000000) (15963049557 / 1000000000000), orderedInterval (78117025005 / 1000000000000) (78117025007 / 1000000000000)))) (orderedInterval (-6028035115 / 1000000000000) (-6028035047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (5409532976328369 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-98957735372 / 1000000000000) (-98957697942 / 1000000000000), orderedInterval (73770219245 / 1000000000000) (73770256675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (21989451220484049 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12710043648 / 1000000000000) (12710043740 / 1000000000000), orderedInterval (-59570306920 / 1000000000000) (-59570306828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (14687934334756191 / 128000000000000) 1 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48275598641 / 1000000000000) (48275632382 / 1000000000000), orderedInterval (-56932342417 / 1000000000000) (-56932308676 / 1000000000000)))) (orderedInterval (22487065976 / 1000000000000) (22487073992 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks1 :
    compactCertificate203.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate203.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate203_chunkChecks1_0
    compactCertificate203_chunkChecks1_1 compactCertificate203_chunkChecks1_2

theorem compactCertificate203_chunkChecks2_0 :
    compactCertificate203.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (5913 / 64) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-72938732978 / 1000000000000) (-72938719811 / 1000000000000), orderedInterval (40023119794 / 1000000000000) (40023132961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (8710978074938613 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26445826642 / 1000000000000) (-26445826195 / 1000000000000), orderedInterval (93228629945 / 1000000000000) (93228630391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (2816951331095829 / 25600000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57924051532 / 1000000000000) (-57924051531 / 1000000000000), orderedInterval (-49034801792 / 1000000000000) (-49034801791 / 1000000000000)))) (orderedInterval (33724002006 / 1000000000000) (33724007293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (2541841676778591 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174825801902 / 1000000000000) (174825802309 / 1000000000000), orderedInterval (-42936602671 / 1000000000000) (-42936602265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (6827744283435027 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71847271846 / 1000000000000) (-71847271845 / 1000000000000), orderedInterval (-81623480685 / 1000000000000) (-81623480684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (18538653914941959 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (59220771271 / 1000000000000) (59220771272 / 1000000000000), orderedInterval (29601952965 / 1000000000000) (29601952966 / 1000000000000)))) (orderedInterval (11361020909 / 1000000000000) (11361020928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (13655488566875967 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46969533926 / 1000000000000) (46969533927 / 1000000000000), orderedInterval (61108887106 / 1000000000000) (61108887107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (23398912409688891 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57900643592 / 1000000000000) (57900643595 / 1000000000000), orderedInterval (11244696124 / 1000000000000) (11244696127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (17235532976328369 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23486118916 / 1000000000000) (-23486118915 / 1000000000000), orderedInterval (-64537055607 / 1000000000000) (-64537055606 / 1000000000000)))) (orderedInterval (8229184604 / 1000000000000) (8229184621 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks2_1 :
    compactCertificate203.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (26443739901909087 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1742550528 / 1000000000000) (1742550530 / 1000000000000), orderedInterval (55480089546 / 1000000000000) (55480089548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (15267300350746023 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45915783817 / 1000000000000) (45915783818 / 1000000000000), orderedInterval (56632935733 / 1000000000000) (56632935734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (27092092387925907 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-50843554036 / 1000000000000) (-50843546324 / 1000000000000), orderedInterval (20680200716 / 1000000000000) (20680208428 / 1000000000000)))) (orderedInterval (33917620301 / 1000000000000) (33917626248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (25312947002593983 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33051023597 / 1000000000000) (-33051023596 / 1000000000000), orderedInterval (-46033990908 / 1000000000000) (-46033990907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (18064513389510639 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34637690379 / 1000000000000) (-34637690378 / 1000000000000), orderedInterval (-57419879397 / 1000000000000) (-57419879396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (20483232850305081 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35020588120 / 1000000000000) (-35020588119 / 1000000000000), orderedInterval (-52348290050 / 1000000000000) (-52348290049 / 1000000000000)))) (orderedInterval (4442901710 / 1000000000000) (4442901741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (17076784066210089 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (53750159659 / 1000000000000) (53750242168 / 1000000000000), orderedInterval (-43591895134 / 1000000000000) (-43591812625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (15087856609399869 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-48585448423 / 1000000000000) (-48585409570 / 1000000000000), orderedInterval (55345140272 / 1000000000000) (55345179124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (4373048922863031 / 25600000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56461163274 / 1000000000000) (56461169905 / 1000000000000), orderedInterval (-23379967677 / 1000000000000) (-23379961046 / 1000000000000)))) (orderedInterval (-10698181159 / 1000000000000) (-10698174904 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks2_2 :
    compactCertificate203.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (12096083461595157 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70656110232 / 1000000000000) (70656110233 / 1000000000000), orderedInterval (41391459618 / 1000000000000) (41391459619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (10253983910850477 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63218729848 / 1000000000000) (-63218648469 / 1000000000000), orderedInterval (63245858819 / 1000000000000) (63245940198 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (6416467023671631 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67845619680 / 1000000000000) (67845619681 / 1000000000000), orderedInterval (89305933734 / 1000000000000) (89305933735 / 1000000000000)))) (orderedInterval (8568744921 / 1000000000000) (8568748448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (3450797305536177 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78236085126 / 1000000000000) (78236094918 / 1000000000000), orderedInterval (-133719645172 / 1000000000000) (-133719635380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (9369585960219531 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92121969512 / 1000000000000) (-92121969265 / 1000000000000), orderedInterval (15132812497 / 1000000000000) (15132812745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (12793368598137387 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15963049556 / 1000000000000) (15963049557 / 1000000000000), orderedInterval (78117025005 / 1000000000000) (78117025007 / 1000000000000)))) (orderedInterval (308067133 / 1000000000000) (308067164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (5409532976328369 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-98957735372 / 1000000000000) (-98957697942 / 1000000000000), orderedInterval (73770219245 / 1000000000000) (73770256675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (21989451220484049 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12710043648 / 1000000000000) (12710043740 / 1000000000000), orderedInterval (-59570306920 / 1000000000000) (-59570306828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (14687934334756191 / 128000000000000) 2 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48275598641 / 1000000000000) (48275632382 / 1000000000000), orderedInterval (-56932342417 / 1000000000000) (-56932308676 / 1000000000000)))) (orderedInterval (17430844520 / 1000000000000) (17430854499 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks2 :
    compactCertificate203.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate203.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate203_chunkChecks2_0
    compactCertificate203_chunkChecks2_1 compactCertificate203_chunkChecks2_2

theorem compactCertificate203_chunkChecks3_0 :
    compactCertificate203.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (5913 / 64) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-72938732978 / 1000000000000) (-72938719811 / 1000000000000), orderedInterval (40023119794 / 1000000000000) (40023132961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (8710978074938613 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26445826642 / 1000000000000) (-26445826195 / 1000000000000), orderedInterval (93228629945 / 1000000000000) (93228630391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (2816951331095829 / 25600000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57924051532 / 1000000000000) (-57924051531 / 1000000000000), orderedInterval (-49034801792 / 1000000000000) (-49034801791 / 1000000000000)))) (orderedInterval (-11713306455 / 1000000000000) (-11713301168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (2541841676778591 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174825801902 / 1000000000000) (174825802309 / 1000000000000), orderedInterval (-42936602671 / 1000000000000) (-42936602265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (6827744283435027 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71847271846 / 1000000000000) (-71847271845 / 1000000000000), orderedInterval (-81623480685 / 1000000000000) (-81623480684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (18538653914941959 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (59220771271 / 1000000000000) (59220771272 / 1000000000000), orderedInterval (29601952965 / 1000000000000) (29601952966 / 1000000000000)))) (orderedInterval (8552139981 / 1000000000000) (8552140008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (13655488566875967 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46969533926 / 1000000000000) (46969533927 / 1000000000000), orderedInterval (61108887106 / 1000000000000) (61108887107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (23398912409688891 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57900643592 / 1000000000000) (57900643595 / 1000000000000), orderedInterval (11244696124 / 1000000000000) (11244696127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (17235532976328369 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23486118916 / 1000000000000) (-23486118915 / 1000000000000), orderedInterval (-64537055607 / 1000000000000) (-64537055606 / 1000000000000)))) (orderedInterval (7425599466 / 1000000000000) (7425599496 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks3_1 :
    compactCertificate203.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (26443739901909087 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1742550528 / 1000000000000) (1742550530 / 1000000000000), orderedInterval (55480089546 / 1000000000000) (55480089548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (15267300350746023 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45915783817 / 1000000000000) (45915783818 / 1000000000000), orderedInterval (56632935733 / 1000000000000) (56632935734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (27092092387925907 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-50843554036 / 1000000000000) (-50843546324 / 1000000000000), orderedInterval (20680200716 / 1000000000000) (20680208428 / 1000000000000)))) (orderedInterval (65475207000 / 1000000000000) (65475220605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (25312947002593983 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33051023597 / 1000000000000) (-33051023596 / 1000000000000), orderedInterval (-46033990908 / 1000000000000) (-46033990907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (18064513389510639 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34637690379 / 1000000000000) (-34637690378 / 1000000000000), orderedInterval (-57419879397 / 1000000000000) (-57419879396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (20483232850305081 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35020588120 / 1000000000000) (-35020588119 / 1000000000000), orderedInterval (-52348290050 / 1000000000000) (-52348290049 / 1000000000000)))) (orderedInterval (9777911267 / 1000000000000) (9777911319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (17076784066210089 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (53750159659 / 1000000000000) (53750242168 / 1000000000000), orderedInterval (-43591895134 / 1000000000000) (-43591812625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (15087856609399869 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-48585448423 / 1000000000000) (-48585409570 / 1000000000000), orderedInterval (55345140272 / 1000000000000) (55345179124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (4373048922863031 / 25600000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56461163274 / 1000000000000) (56461169905 / 1000000000000), orderedInterval (-23379967677 / 1000000000000) (-23379961046 / 1000000000000)))) (orderedInterval (11991618738 / 1000000000000) (11991627393 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks3_2 :
    compactCertificate203.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (12096083461595157 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70656110232 / 1000000000000) (70656110233 / 1000000000000), orderedInterval (41391459618 / 1000000000000) (41391459619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (10253983910850477 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63218729848 / 1000000000000) (-63218648469 / 1000000000000), orderedInterval (63245858819 / 1000000000000) (63245940198 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (6416467023671631 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67845619680 / 1000000000000) (67845619681 / 1000000000000), orderedInterval (89305933734 / 1000000000000) (89305933735 / 1000000000000)))) (orderedInterval (8857482135 / 1000000000000) (8857485195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (3450797305536177 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78236085126 / 1000000000000) (78236094918 / 1000000000000), orderedInterval (-133719645172 / 1000000000000) (-133719635380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (9369585960219531 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92121969512 / 1000000000000) (-92121969265 / 1000000000000), orderedInterval (15132812497 / 1000000000000) (15132812745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (12793368598137387 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15963049556 / 1000000000000) (15963049557 / 1000000000000), orderedInterval (78117025005 / 1000000000000) (78117025007 / 1000000000000)))) (orderedInterval (7684773866 / 1000000000000) (7684773884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (5409532976328369 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-98957735372 / 1000000000000) (-98957697942 / 1000000000000), orderedInterval (73770219245 / 1000000000000) (73770256675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (21989451220484049 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12710043648 / 1000000000000) (12710043740 / 1000000000000), orderedInterval (-59570306920 / 1000000000000) (-59570306828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (14687934334756191 / 128000000000000) 3 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48275598641 / 1000000000000) (48275632382 / 1000000000000), orderedInterval (-56932342417 / 1000000000000) (-56932308676 / 1000000000000)))) (orderedInterval (-51868123075 / 1000000000000) (-51868110689 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks3 :
    compactCertificate203.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate203.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate203_chunkChecks3_0
    compactCertificate203_chunkChecks3_1 compactCertificate203_chunkChecks3_2

theorem compactCertificate203_chunkChecks4_0 :
    compactCertificate203.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (5913 / 64) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-72938732978 / 1000000000000) (-72938719811 / 1000000000000), orderedInterval (40023119794 / 1000000000000) (40023132961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (8710978074938613 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26445826642 / 1000000000000) (-26445826195 / 1000000000000), orderedInterval (93228629945 / 1000000000000) (93228630391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (2816951331095829 / 25600000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57924051532 / 1000000000000) (-57924051531 / 1000000000000), orderedInterval (-49034801792 / 1000000000000) (-49034801791 / 1000000000000)))) (orderedInterval (-35564578853 / 1000000000000) (-35564573509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (2541841676778591 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (174825801902 / 1000000000000) (174825802309 / 1000000000000), orderedInterval (-42936602671 / 1000000000000) (-42936602265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (6827744283435027 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71847271846 / 1000000000000) (-71847271845 / 1000000000000), orderedInterval (-81623480685 / 1000000000000) (-81623480684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (18538653914941959 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (59220771271 / 1000000000000) (59220771272 / 1000000000000), orderedInterval (29601952965 / 1000000000000) (29601952966 / 1000000000000)))) (orderedInterval (-25903185933 / 1000000000000) (-25903185891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (13655488566875967 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46969533926 / 1000000000000) (46969533927 / 1000000000000), orderedInterval (61108887106 / 1000000000000) (61108887107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (23398912409688891 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (57900643592 / 1000000000000) (57900643595 / 1000000000000), orderedInterval (11244696124 / 1000000000000) (11244696127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (17235532976328369 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23486118916 / 1000000000000) (-23486118915 / 1000000000000), orderedInterval (-64537055607 / 1000000000000) (-64537055606 / 1000000000000)))) (orderedInterval (-30091379413 / 1000000000000) (-30091379357 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks4_1 :
    compactCertificate203.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (26443739901909087 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1742550528 / 1000000000000) (1742550530 / 1000000000000), orderedInterval (55480089546 / 1000000000000) (55480089548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (15267300350746023 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45915783817 / 1000000000000) (45915783818 / 1000000000000), orderedInterval (56632935733 / 1000000000000) (56632935734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (27092092387925907 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-50843554036 / 1000000000000) (-50843546324 / 1000000000000), orderedInterval (20680200716 / 1000000000000) (20680208428 / 1000000000000)))) (orderedInterval (-198780429573 / 1000000000000) (-198780398292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (25312947002593983 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33051023597 / 1000000000000) (-33051023596 / 1000000000000), orderedInterval (-46033990908 / 1000000000000) (-46033990907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (18064513389510639 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34637690379 / 1000000000000) (-34637690378 / 1000000000000), orderedInterval (-57419879397 / 1000000000000) (-57419879396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (20483232850305081 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35020588120 / 1000000000000) (-35020588119 / 1000000000000), orderedInterval (-52348290050 / 1000000000000) (-52348290049 / 1000000000000)))) (orderedInterval (-3924699766 / 1000000000000) (-3924699677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (17076784066210089 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (53750159659 / 1000000000000) (53750242168 / 1000000000000), orderedInterval (-43591895134 / 1000000000000) (-43591812625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (15087856609399869 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-48585448423 / 1000000000000) (-48585409570 / 1000000000000), orderedInterval (55345140272 / 1000000000000) (55345179124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (4373048922863031 / 25600000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56461163274 / 1000000000000) (56461169905 / 1000000000000), orderedInterval (-23379967677 / 1000000000000) (-23379961046 / 1000000000000)))) (orderedInterval (26697970892 / 1000000000000) (26697983140 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks4_2 :
    compactCertificate203.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (12096083461595157 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (70656110232 / 1000000000000) (70656110233 / 1000000000000), orderedInterval (41391459618 / 1000000000000) (41391459619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (10253983910850477 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-63218729848 / 1000000000000) (-63218648469 / 1000000000000), orderedInterval (63245858819 / 1000000000000) (63245940198 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (6416467023671631 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67845619680 / 1000000000000) (67845619681 / 1000000000000), orderedInterval (89305933734 / 1000000000000) (89305933735 / 1000000000000)))) (orderedInterval (-10342166150 / 1000000000000) (-10342163462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (3450797305536177 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78236085126 / 1000000000000) (78236094918 / 1000000000000), orderedInterval (-133719645172 / 1000000000000) (-133719635380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (9369585960219531 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92121969512 / 1000000000000) (-92121969265 / 1000000000000), orderedInterval (15132812497 / 1000000000000) (15132812745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (12793368598137387 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15963049556 / 1000000000000) (15963049557 / 1000000000000), orderedInterval (78117025005 / 1000000000000) (78117025007 / 1000000000000)))) (orderedInterval (-1028809213 / 1000000000000) (-1028809198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (5409532976328369 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-98957735372 / 1000000000000) (-98957697942 / 1000000000000), orderedInterval (73770219245 / 1000000000000) (73770256675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (21989451220484049 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12710043648 / 1000000000000) (12710043740 / 1000000000000), orderedInterval (-59570306920 / 1000000000000) (-59570306828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (14687934334756191 / 128000000000000) 4 (IntervalRat.scale (5913 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48275598641 / 1000000000000) (48275632382 / 1000000000000), orderedInterval (-56932342417 / 1000000000000) (-56932308676 / 1000000000000)))) (orderedInterval (-32822239939 / 1000000000000) (-32822224382 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate203_chunkChecks4 :
    compactCertificate203.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate203.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate203_chunkChecks4_0
    compactCertificate203_chunkChecks4_1 compactCertificate203_chunkChecks4_2

theorem compactCertificate203_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate203.chunkCheck r b = true :=
  compactCertificate203.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate203_chunkChecks0
    · exact compactCertificate203_chunkChecks1
    · exact compactCertificate203_chunkChecks2
    · exact compactCertificate203_chunkChecks3
    · exact compactCertificate203_chunkChecks4)

theorem compactCertificate203_coefficient0 :
    compactCertificate203.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate203, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate203_coefficient1 :
    compactCertificate203.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate203, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate203_coefficient2 :
    compactCertificate203.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate203, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate203_coefficient3 :
    compactCertificate203.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate203, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate203_coefficient4 :
    compactCertificate203.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate203, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate203_coefficients : ∀ r : Fin 5,
    compactCertificate203.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate203_coefficient0
  · exact compactCertificate203_coefficient1
  · exact compactCertificate203_coefficient2
  · exact compactCertificate203_coefficient3
  · exact compactCertificate203_coefficient4

theorem compactCertificate203_lower : (1 : ℚ) ≤ compactCertificate203.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate203, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate203_proves {t : ℝ} (ht : t ∈ compactCertificate203.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate203.proves compactCertificate203_states compactCertificate203_chunks
    compactCertificate203_coefficients compactCertificate203_lower ht

end Erdos232
