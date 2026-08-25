/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate265 : CompactCertificate where
  left := 139
  right := 140
  center := 279 / 2
  grid := fun i =>
    match i.val with
    | 0 => 44
    | 1 => 33
    | 2 => 53
    | 3 => 10
    | 4 => 26
    | 5 => 70
    | 6 => 51
    | 7 => 88
    | 8 => 65
    | 9 => 99
    | 10 => 57
    | 11 => 102
    | 12 => 95
    | 13 => 68
    | 14 => 77
    | 15 => 64
    | 16 => 57
    | 17 => 82
    | 18 => 45
    | 19 => 39
    | 20 => 24
    | 21 => 13
    | 22 => 35
    | 23 => 48
    | 24 => 20
    | 25 => 83
    | _ => 55
  point := fun i =>
    match i.val with
    | 0 => 279 / 2
    | 1 => 411020274464379 / 4000000000000
    | 2 => 132915511817307 / 800000000000
    | 3 => 119934690989553 / 4000000000000
    | 4 => 322161450207741 / 4000000000000
    | 5 => 874731006641097 / 4000000000000
    | 6 => 644322900415761 / 4000000000000
    | 7 => 1104058271994453 / 4000000000000
    | 8 => 813244326128127 / 4000000000000
    | 9 => 1247725931444721 / 4000000000000
    | 10 => 720374902394409 / 4000000000000
    | 11 => 1278317905670781 / 4000000000000
    | 12 => 1194370406515089 / 4000000000000
    | 13 => 852359079261537 / 4000000000000
    | 14 => 966484350623223 / 4000000000000
    | 15 => 805753890490887 / 4000000000000
    | 16 => 711907998312627 / 4000000000000
    | 17 => 206338685858073 / 800000000000
    | 18 => 570743664093531 / 4000000000000
    | 19 => 483825724865091 / 4000000000000
    | 20 => 302755673871873 / 4000000000000
    | 21 => 162823008328191 / 4000000000000
    | 22 => 442096141197573 / 4000000000000
    | 23 => 603644484843621 / 4000000000000
    | 24 => 255244326128127 / 4000000000000
    | 25 => 1037554014969567 / 4000000000000
    | _ => 693037997530353 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (59806512935 / 1000000000000) (59806527361 / 1000000000000), orderedInterval (-31626878949 / 1000000000000) (-31626864523 / 1000000000000))
    | 1 => (orderedInterval (10461704725 / 1000000000000) (10461704775 / 1000000000000), orderedInterval (-78064562153 / 1000000000000) (-78064562103 / 1000000000000))
    | 2 => (orderedInterval (-25501832533 / 1000000000000) (-25501832532 / 1000000000000), orderedInterval (-56327101770 / 1000000000000) (-56327101769 / 1000000000000))
    | 3 => (orderedInterval (-88295803528 / 1000000000000) (-88295773888 / 1000000000000), orderedInterval (117389403889 / 1000000000000) (117389433530 / 1000000000000))
    | 4 => (orderedInterval (-31086064102 / 1000000000000) (-31086062997 / 1000000000000), orderedInterval (83488406130 / 1000000000000) (83488407235 / 1000000000000))
    | 5 => (orderedInterval (-23172166231 / 1000000000000) (-23172164872 / 1000000000000), orderedInterval (48778869802 / 1000000000000) (48778871160 / 1000000000000))
    | 6 => (orderedInterval (-62697273681 / 1000000000000) (-62697273535 / 1000000000000), orderedInterval (4800207946 / 1000000000000) (4800208092 / 1000000000000))
    | 7 => (orderedInterval (15986960595 / 1000000000000) (15986960596 / 1000000000000), orderedInterval (45257811240 / 1000000000000) (45257811241 / 1000000000000))
    | 8 => (orderedInterval (6012627945 / 1000000000000) (6012627961 / 1000000000000), orderedInterval (-55648563641 / 1000000000000) (-55648563625 / 1000000000000))
    | 9 => (orderedInterval (-44806606540 / 1000000000000) (-44806605751 / 1000000000000), orderedInterval (5839115499 / 1000000000000) (5839116289 / 1000000000000))
    | 10 => (orderedInterval (-57795307902 / 1000000000000) (-57795306598 / 1000000000000), orderedInterval (14111306986 / 1000000000000) (14111308290 / 1000000000000))
    | 11 => (orderedInterval (-3476340617 / 1000000000000) (-3476340613 / 1000000000000), orderedInterval (44502316155 / 1000000000000) (44502316159 / 1000000000000))
    | 12 => (orderedInterval (-36911261870 / 1000000000000) (-36911261869 / 1000000000000), orderedInterval (-27680326445 / 1000000000000) (-27680326444 / 1000000000000))
    | 13 => (orderedInterval (13325691065 / 1000000000000) (13325691066 / 1000000000000), orderedInterval (52978158935 / 1000000000000) (52978158936 / 1000000000000))
    | 14 => (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))
    | 15 => (orderedInterval (51569579949 / 1000000000000) (51569579950 / 1000000000000), orderedInterval (22253689108 / 1000000000000) (22253689109 / 1000000000000))
    | 16 => (orderedInterval (18192786710 / 1000000000000) (18192787045 / 1000000000000), orderedInterval (-57024891258 / 1000000000000) (-57024890923 / 1000000000000))
    | 17 => (orderedInterval (44223925694 / 1000000000000) (44223925695 / 1000000000000), orderedInterval (22552586917 / 1000000000000) (22552586918 / 1000000000000))
    | 18 => (orderedInterval (-57700116630 / 1000000000000) (-57700094277 / 1000000000000), orderedInterval (33852890463 / 1000000000000) (33852912817 / 1000000000000))
    | 19 => (orderedInterval (51089185306 / 1000000000000) (51089249776 / 1000000000000), orderedInterval (-51719541305 / 1000000000000) (-51719476835 / 1000000000000))
    | 20 => (orderedInterval (80643298190 / 1000000000000) (80643298191 / 1000000000000), orderedInterval (43142938835 / 1000000000000) (43142938836 / 1000000000000))
    | 21 => (orderedInterval (-75419171902 / 1000000000000) (-75419171901 / 1000000000000), orderedInterval (-98832568829 / 1000000000000) (-98832568828 / 1000000000000))
    | 22 => (orderedInterval (-74094197132 / 1000000000000) (-74094197131 / 1000000000000), orderedInterval (-16096749357 / 1000000000000) (-16096749355 / 1000000000000))
    | 23 => (orderedInterval (50846428090 / 1000000000000) (50846428091 / 1000000000000), orderedInterval (40243707552 / 1000000000000) (40243707553 / 1000000000000))
    | 24 => (orderedInterval (98048643678 / 1000000000000) (98048644050 / 1000000000000), orderedInterval (-19815877677 / 1000000000000) (-19815877305 / 1000000000000))
    | 25 => (orderedInterval (27098641119 / 1000000000000) (27098645932 / 1000000000000), orderedInterval (-41524822018 / 1000000000000) (-41524817204 / 1000000000000))
    | _ => (orderedInterval (-57648621075 / 1000000000000) (-57648621073 / 1000000000000), orderedInterval (-18568514187 / 1000000000000) (-18568514186 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (22306214263 / 1000000000000) (22306219992 / 1000000000000)
      | 1 => orderedInterval (1470240942 / 1000000000000) (1470241418 / 1000000000000)
      | 2 => orderedInterval (-347788478 / 1000000000000) (-347788469 / 1000000000000)
      | 3 => orderedInterval (3185253800 / 1000000000000) (3185254093 / 1000000000000)
      | 4 => orderedInterval (2051772615 / 1000000000000) (2051772632 / 1000000000000)
      | 5 => orderedInterval (686702919 / 1000000000000) (686702952 / 1000000000000)
      | 6 => orderedInterval (8959524097 / 1000000000000) (8959531356 / 1000000000000)
      | 7 => orderedInterval (-823224143 / 1000000000000) (-823224125 / 1000000000000)
      | _ => orderedInterval (9201601989 / 1000000000000) (9201602423 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17008250370 / 1000000000000) (-17008244640 / 1000000000000)
      | 1 => orderedInterval (-3949787328 / 1000000000000) (-3949787064 / 1000000000000)
      | 2 => orderedInterval (-4722106712 / 1000000000000) (-4722106697 / 1000000000000)
      | 3 => orderedInterval (13522559713 / 1000000000000) (13522560268 / 1000000000000)
      | 4 => orderedInterval (9115829828 / 1000000000000) (9115829856 / 1000000000000)
      | 5 => orderedInterval (5602148486 / 1000000000000) (5602148530 / 1000000000000)
      | 6 => orderedInterval (-2236188715 / 1000000000000) (-2236181862 / 1000000000000)
      | 7 => orderedInterval (-2514674534 / 1000000000000) (-2514674518 / 1000000000000)
      | _ => orderedInterval (10557616426 / 1000000000000) (10557617211 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-21513461611 / 1000000000000) (-21513455838 / 1000000000000)
      | 1 => orderedInterval (-3685727761 / 1000000000000) (-3685727466 / 1000000000000)
      | 2 => orderedInterval (1655612795 / 1000000000000) (1655612821 / 1000000000000)
      | 3 => orderedInterval (-30174411875 / 1000000000000) (-30174410760 / 1000000000000)
      | 4 => orderedInterval (-6434453029 / 1000000000000) (-6434452983 / 1000000000000)
      | 5 => orderedInterval (-3458010630 / 1000000000000) (-3458010569 / 1000000000000)
      | 6 => orderedInterval (-8234888394 / 1000000000000) (-8234881831 / 1000000000000)
      | 7 => orderedInterval (3404684425 / 1000000000000) (3404684441 / 1000000000000)
      | _ => orderedInterval (-9257797893 / 1000000000000) (-9257796451 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18563904422 / 1000000000000) (18563910196 / 1000000000000)
      | 1 => orderedInterval (12810758015 / 1000000000000) (12810758440 / 1000000000000)
      | 2 => orderedInterval (14964148450 / 1000000000000) (14964148497 / 1000000000000)
      | 3 => orderedInterval (-66493481123 / 1000000000000) (-66493478794 / 1000000000000)
      | 4 => orderedInterval (-23890817980 / 1000000000000) (-23890817903 / 1000000000000)
      | 5 => orderedInterval (-11175251523 / 1000000000000) (-11175251438 / 1000000000000)
      | 6 => orderedInterval (3718539507 / 1000000000000) (3718545787 / 1000000000000)
      | 7 => orderedInterval (3653208951 / 1000000000000) (3653208967 / 1000000000000)
      | _ => orderedInterval (-28327060618 / 1000000000000) (-28327057964 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (20455621937 / 1000000000000) (20455627754 / 1000000000000)
      | 1 => orderedInterval (9640042242 / 1000000000000) (9640042898 / 1000000000000)
      | 2 => orderedInterval (-7116151734 / 1000000000000) (-7116151650 / 1000000000000)
      | 3 => orderedInterval (174485200135 / 1000000000000) (174485205146 / 1000000000000)
      | 4 => orderedInterval (22317634316 / 1000000000000) (22317634449 / 1000000000000)
      | 5 => orderedInterval (13222956437 / 1000000000000) (13222956560 / 1000000000000)
      | 6 => orderedInterval (8637285815 / 1000000000000) (8637291908 / 1000000000000)
      | 7 => orderedInterval (-4716757869 / 1000000000000) (-4716757852 / 1000000000000)
      | _ => orderedInterval (-199122185 / 1000000000000) (-199117266 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (46690298004 / 1000000000000) (46690312272 / 1000000000000)
    | 1 => orderedInterval (8367146794 / 1000000000000) (8367161084 / 1000000000000)
    | 2 => orderedInterval (-77698453973 / 1000000000000) (-77698438636 / 1000000000000)
    | 3 => orderedInterval (-76176051899 / 1000000000000) (-76176034212 / 1000000000000)
    | _ => orderedInterval (236726709094 / 1000000000000) (236726731947 / 1000000000000)

theorem compactCertificate265_stateChecks0 :
    compactCertificate265.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (279 / 2)) (orderedInterval (59806512935 / 1000000000000) (59806527361 / 1000000000000), orderedInterval (-31626878949 / 1000000000000) (-31626864523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (411020274464379 / 4000000000000)) (orderedInterval (10461704725 / 1000000000000) (10461704775 / 1000000000000), orderedInterval (-78064562153 / 1000000000000) (-78064562103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (132915511817307 / 800000000000)) (orderedInterval (-25501832533 / 1000000000000) (-25501832532 / 1000000000000), orderedInterval (-56327101770 / 1000000000000) (-56327101769 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_stateChecks1 :
    compactCertificate265.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (119934690989553 / 4000000000000)) (orderedInterval (-88295803528 / 1000000000000) (-88295773888 / 1000000000000), orderedInterval (117389403889 / 1000000000000) (117389433530 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (322161450207741 / 4000000000000)) (orderedInterval (-31086064102 / 1000000000000) (-31086062997 / 1000000000000), orderedInterval (83488406130 / 1000000000000) (83488407235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (874731006641097 / 4000000000000)) (orderedInterval (-23172166231 / 1000000000000) (-23172164872 / 1000000000000), orderedInterval (48778869802 / 1000000000000) (48778871160 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_stateChecks2 :
    compactCertificate265.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (644322900415761 / 4000000000000)) (orderedInterval (-62697273681 / 1000000000000) (-62697273535 / 1000000000000), orderedInterval (4800207946 / 1000000000000) (4800208092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1104058271994453 / 4000000000000)) (orderedInterval (15986960595 / 1000000000000) (15986960596 / 1000000000000), orderedInterval (45257811240 / 1000000000000) (45257811241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (813244326128127 / 4000000000000)) (orderedInterval (6012627945 / 1000000000000) (6012627961 / 1000000000000), orderedInterval (-55648563641 / 1000000000000) (-55648563625 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_stateChecks3 :
    compactCertificate265.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1247725931444721 / 4000000000000)) (orderedInterval (-44806606540 / 1000000000000) (-44806605751 / 1000000000000), orderedInterval (5839115499 / 1000000000000) (5839116289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (720374902394409 / 4000000000000)) (orderedInterval (-57795307902 / 1000000000000) (-57795306598 / 1000000000000), orderedInterval (14111306986 / 1000000000000) (14111308290 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1278317905670781 / 4000000000000)) (orderedInterval (-3476340617 / 1000000000000) (-3476340613 / 1000000000000), orderedInterval (44502316155 / 1000000000000) (44502316159 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_stateChecks4 :
    compactCertificate265.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1194370406515089 / 4000000000000)) (orderedInterval (-36911261870 / 1000000000000) (-36911261869 / 1000000000000), orderedInterval (-27680326445 / 1000000000000) (-27680326444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (852359079261537 / 4000000000000)) (orderedInterval (13325691065 / 1000000000000) (13325691066 / 1000000000000), orderedInterval (52978158935 / 1000000000000) (52978158936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (966484350623223 / 4000000000000)) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_stateChecks5 :
    compactCertificate265.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (805753890490887 / 4000000000000)) (orderedInterval (51569579949 / 1000000000000) (51569579950 / 1000000000000), orderedInterval (22253689108 / 1000000000000) (22253689109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (711907998312627 / 4000000000000)) (orderedInterval (18192786710 / 1000000000000) (18192787045 / 1000000000000), orderedInterval (-57024891258 / 1000000000000) (-57024890923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (206338685858073 / 800000000000)) (orderedInterval (44223925694 / 1000000000000) (44223925695 / 1000000000000), orderedInterval (22552586917 / 1000000000000) (22552586918 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_stateChecks6 :
    compactCertificate265.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (570743664093531 / 4000000000000)) (orderedInterval (-57700116630 / 1000000000000) (-57700094277 / 1000000000000), orderedInterval (33852890463 / 1000000000000) (33852912817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (483825724865091 / 4000000000000)) (orderedInterval (51089185306 / 1000000000000) (51089249776 / 1000000000000), orderedInterval (-51719541305 / 1000000000000) (-51719476835 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (302755673871873 / 4000000000000)) (orderedInterval (80643298190 / 1000000000000) (80643298191 / 1000000000000), orderedInterval (43142938835 / 1000000000000) (43142938836 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_stateChecks7 :
    compactCertificate265.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (162823008328191 / 4000000000000)) (orderedInterval (-75419171902 / 1000000000000) (-75419171901 / 1000000000000), orderedInterval (-98832568829 / 1000000000000) (-98832568828 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (442096141197573 / 4000000000000)) (orderedInterval (-74094197132 / 1000000000000) (-74094197131 / 1000000000000), orderedInterval (-16096749357 / 1000000000000) (-16096749355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (603644484843621 / 4000000000000)) (orderedInterval (50846428090 / 1000000000000) (50846428091 / 1000000000000), orderedInterval (40243707552 / 1000000000000) (40243707553 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_stateChecks8 :
    compactCertificate265.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (255244326128127 / 4000000000000)) (orderedInterval (98048643678 / 1000000000000) (98048644050 / 1000000000000), orderedInterval (-19815877677 / 1000000000000) (-19815877305 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1037554014969567 / 4000000000000)) (orderedInterval (27098641119 / 1000000000000) (27098645932 / 1000000000000), orderedInterval (-41524822018 / 1000000000000) (-41524817204 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (693037997530353 / 4000000000000)) (orderedInterval (-57648621075 / 1000000000000) (-57648621073 / 1000000000000), orderedInterval (-18568514187 / 1000000000000) (-18568514186 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState013, besselGridState020, besselGridState024, besselGridState026, besselGridState033, besselGridState035, besselGridState039, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState057, besselGridState064, besselGridState065, besselGridState068, besselGridState070, besselGridState077, besselGridState082, besselGridState083, besselGridState088, besselGridState095, besselGridState099, besselGridState102, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate265_states : ∀ j,
    BesselStateValid (compactCertificate265.point j) (compactCertificate265.state j) :=
  compactCertificate265.statesValid_of_checks3 compactCertificate265_stateChecks0
    compactCertificate265_stateChecks1 compactCertificate265_stateChecks2
    compactCertificate265_stateChecks3 compactCertificate265_stateChecks4
    compactCertificate265_stateChecks5 compactCertificate265_stateChecks6
    compactCertificate265_stateChecks7 compactCertificate265_stateChecks8

theorem compactCertificate265_chunkChecks0_0 :
    compactCertificate265.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (279 / 2) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59806512935 / 1000000000000) (59806527361 / 1000000000000), orderedInterval (-31626878949 / 1000000000000) (-31626864523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (411020274464379 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10461704725 / 1000000000000) (10461704775 / 1000000000000), orderedInterval (-78064562153 / 1000000000000) (-78064562103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (132915511817307 / 800000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25501832533 / 1000000000000) (-25501832532 / 1000000000000), orderedInterval (-56327101770 / 1000000000000) (-56327101769 / 1000000000000)))) (orderedInterval (22306214263 / 1000000000000) (22306219992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (119934690989553 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88295803528 / 1000000000000) (-88295773888 / 1000000000000), orderedInterval (117389403889 / 1000000000000) (117389433530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (322161450207741 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31086064102 / 1000000000000) (-31086062997 / 1000000000000), orderedInterval (83488406130 / 1000000000000) (83488407235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (874731006641097 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23172166231 / 1000000000000) (-23172164872 / 1000000000000), orderedInterval (48778869802 / 1000000000000) (48778871160 / 1000000000000)))) (orderedInterval (1470240942 / 1000000000000) (1470241418 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (644322900415761 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-62697273681 / 1000000000000) (-62697273535 / 1000000000000), orderedInterval (4800207946 / 1000000000000) (4800208092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1104058271994453 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15986960595 / 1000000000000) (15986960596 / 1000000000000), orderedInterval (45257811240 / 1000000000000) (45257811241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (813244326128127 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6012627945 / 1000000000000) (6012627961 / 1000000000000), orderedInterval (-55648563641 / 1000000000000) (-55648563625 / 1000000000000)))) (orderedInterval (-347788478 / 1000000000000) (-347788469 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks0_1 :
    compactCertificate265.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1247725931444721 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-44806606540 / 1000000000000) (-44806605751 / 1000000000000), orderedInterval (5839115499 / 1000000000000) (5839116289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (720374902394409 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57795307902 / 1000000000000) (-57795306598 / 1000000000000), orderedInterval (14111306986 / 1000000000000) (14111308290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1278317905670781 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3476340617 / 1000000000000) (-3476340613 / 1000000000000), orderedInterval (44502316155 / 1000000000000) (44502316159 / 1000000000000)))) (orderedInterval (3185253800 / 1000000000000) (3185254093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1194370406515089 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36911261870 / 1000000000000) (-36911261869 / 1000000000000), orderedInterval (-27680326445 / 1000000000000) (-27680326444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (852359079261537 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13325691065 / 1000000000000) (13325691066 / 1000000000000), orderedInterval (52978158935 / 1000000000000) (52978158936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000)))) (orderedInterval (2051772615 / 1000000000000) (2051772632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (805753890490887 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51569579949 / 1000000000000) (51569579950 / 1000000000000), orderedInterval (22253689108 / 1000000000000) (22253689109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (711907998312627 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18192786710 / 1000000000000) (18192787045 / 1000000000000), orderedInterval (-57024891258 / 1000000000000) (-57024890923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (206338685858073 / 800000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (44223925694 / 1000000000000) (44223925695 / 1000000000000), orderedInterval (22552586917 / 1000000000000) (22552586918 / 1000000000000)))) (orderedInterval (686702919 / 1000000000000) (686702952 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks0_2 :
    compactCertificate265.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (570743664093531 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-57700116630 / 1000000000000) (-57700094277 / 1000000000000), orderedInterval (33852890463 / 1000000000000) (33852912817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (483825724865091 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51089185306 / 1000000000000) (51089249776 / 1000000000000), orderedInterval (-51719541305 / 1000000000000) (-51719476835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (302755673871873 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80643298190 / 1000000000000) (80643298191 / 1000000000000), orderedInterval (43142938835 / 1000000000000) (43142938836 / 1000000000000)))) (orderedInterval (8959524097 / 1000000000000) (8959531356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (162823008328191 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75419171902 / 1000000000000) (-75419171901 / 1000000000000), orderedInterval (-98832568829 / 1000000000000) (-98832568828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (442096141197573 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-74094197132 / 1000000000000) (-74094197131 / 1000000000000), orderedInterval (-16096749357 / 1000000000000) (-16096749355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (603644484843621 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50846428090 / 1000000000000) (50846428091 / 1000000000000), orderedInterval (40243707552 / 1000000000000) (40243707553 / 1000000000000)))) (orderedInterval (-823224143 / 1000000000000) (-823224125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (255244326128127 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98048643678 / 1000000000000) (98048644050 / 1000000000000), orderedInterval (-19815877677 / 1000000000000) (-19815877305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1037554014969567 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27098641119 / 1000000000000) (27098645932 / 1000000000000), orderedInterval (-41524822018 / 1000000000000) (-41524817204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (693037997530353 / 4000000000000) 0 (IntervalRat.scale (279 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-57648621075 / 1000000000000) (-57648621073 / 1000000000000), orderedInterval (-18568514187 / 1000000000000) (-18568514186 / 1000000000000)))) (orderedInterval (9201601989 / 1000000000000) (9201602423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks0 :
    compactCertificate265.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate265.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate265_chunkChecks0_0
    compactCertificate265_chunkChecks0_1 compactCertificate265_chunkChecks0_2

theorem compactCertificate265_chunkChecks1_0 :
    compactCertificate265.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (279 / 2) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59806512935 / 1000000000000) (59806527361 / 1000000000000), orderedInterval (-31626878949 / 1000000000000) (-31626864523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (411020274464379 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10461704725 / 1000000000000) (10461704775 / 1000000000000), orderedInterval (-78064562153 / 1000000000000) (-78064562103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (132915511817307 / 800000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25501832533 / 1000000000000) (-25501832532 / 1000000000000), orderedInterval (-56327101770 / 1000000000000) (-56327101769 / 1000000000000)))) (orderedInterval (-17008250370 / 1000000000000) (-17008244640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (119934690989553 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88295803528 / 1000000000000) (-88295773888 / 1000000000000), orderedInterval (117389403889 / 1000000000000) (117389433530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (322161450207741 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31086064102 / 1000000000000) (-31086062997 / 1000000000000), orderedInterval (83488406130 / 1000000000000) (83488407235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (874731006641097 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23172166231 / 1000000000000) (-23172164872 / 1000000000000), orderedInterval (48778869802 / 1000000000000) (48778871160 / 1000000000000)))) (orderedInterval (-3949787328 / 1000000000000) (-3949787064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (644322900415761 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-62697273681 / 1000000000000) (-62697273535 / 1000000000000), orderedInterval (4800207946 / 1000000000000) (4800208092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1104058271994453 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15986960595 / 1000000000000) (15986960596 / 1000000000000), orderedInterval (45257811240 / 1000000000000) (45257811241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (813244326128127 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6012627945 / 1000000000000) (6012627961 / 1000000000000), orderedInterval (-55648563641 / 1000000000000) (-55648563625 / 1000000000000)))) (orderedInterval (-4722106712 / 1000000000000) (-4722106697 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks1_1 :
    compactCertificate265.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1247725931444721 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-44806606540 / 1000000000000) (-44806605751 / 1000000000000), orderedInterval (5839115499 / 1000000000000) (5839116289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (720374902394409 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57795307902 / 1000000000000) (-57795306598 / 1000000000000), orderedInterval (14111306986 / 1000000000000) (14111308290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1278317905670781 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3476340617 / 1000000000000) (-3476340613 / 1000000000000), orderedInterval (44502316155 / 1000000000000) (44502316159 / 1000000000000)))) (orderedInterval (13522559713 / 1000000000000) (13522560268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1194370406515089 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36911261870 / 1000000000000) (-36911261869 / 1000000000000), orderedInterval (-27680326445 / 1000000000000) (-27680326444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (852359079261537 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13325691065 / 1000000000000) (13325691066 / 1000000000000), orderedInterval (52978158935 / 1000000000000) (52978158936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000)))) (orderedInterval (9115829828 / 1000000000000) (9115829856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (805753890490887 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51569579949 / 1000000000000) (51569579950 / 1000000000000), orderedInterval (22253689108 / 1000000000000) (22253689109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (711907998312627 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18192786710 / 1000000000000) (18192787045 / 1000000000000), orderedInterval (-57024891258 / 1000000000000) (-57024890923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (206338685858073 / 800000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (44223925694 / 1000000000000) (44223925695 / 1000000000000), orderedInterval (22552586917 / 1000000000000) (22552586918 / 1000000000000)))) (orderedInterval (5602148486 / 1000000000000) (5602148530 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks1_2 :
    compactCertificate265.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (570743664093531 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-57700116630 / 1000000000000) (-57700094277 / 1000000000000), orderedInterval (33852890463 / 1000000000000) (33852912817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (483825724865091 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51089185306 / 1000000000000) (51089249776 / 1000000000000), orderedInterval (-51719541305 / 1000000000000) (-51719476835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (302755673871873 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80643298190 / 1000000000000) (80643298191 / 1000000000000), orderedInterval (43142938835 / 1000000000000) (43142938836 / 1000000000000)))) (orderedInterval (-2236188715 / 1000000000000) (-2236181862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (162823008328191 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75419171902 / 1000000000000) (-75419171901 / 1000000000000), orderedInterval (-98832568829 / 1000000000000) (-98832568828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (442096141197573 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-74094197132 / 1000000000000) (-74094197131 / 1000000000000), orderedInterval (-16096749357 / 1000000000000) (-16096749355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (603644484843621 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50846428090 / 1000000000000) (50846428091 / 1000000000000), orderedInterval (40243707552 / 1000000000000) (40243707553 / 1000000000000)))) (orderedInterval (-2514674534 / 1000000000000) (-2514674518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (255244326128127 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98048643678 / 1000000000000) (98048644050 / 1000000000000), orderedInterval (-19815877677 / 1000000000000) (-19815877305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1037554014969567 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27098641119 / 1000000000000) (27098645932 / 1000000000000), orderedInterval (-41524822018 / 1000000000000) (-41524817204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (693037997530353 / 4000000000000) 1 (IntervalRat.scale (279 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-57648621075 / 1000000000000) (-57648621073 / 1000000000000), orderedInterval (-18568514187 / 1000000000000) (-18568514186 / 1000000000000)))) (orderedInterval (10557616426 / 1000000000000) (10557617211 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks1 :
    compactCertificate265.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate265.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate265_chunkChecks1_0
    compactCertificate265_chunkChecks1_1 compactCertificate265_chunkChecks1_2

theorem compactCertificate265_chunkChecks2_0 :
    compactCertificate265.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (279 / 2) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59806512935 / 1000000000000) (59806527361 / 1000000000000), orderedInterval (-31626878949 / 1000000000000) (-31626864523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (411020274464379 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10461704725 / 1000000000000) (10461704775 / 1000000000000), orderedInterval (-78064562153 / 1000000000000) (-78064562103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (132915511817307 / 800000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25501832533 / 1000000000000) (-25501832532 / 1000000000000), orderedInterval (-56327101770 / 1000000000000) (-56327101769 / 1000000000000)))) (orderedInterval (-21513461611 / 1000000000000) (-21513455838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (119934690989553 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88295803528 / 1000000000000) (-88295773888 / 1000000000000), orderedInterval (117389403889 / 1000000000000) (117389433530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (322161450207741 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31086064102 / 1000000000000) (-31086062997 / 1000000000000), orderedInterval (83488406130 / 1000000000000) (83488407235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (874731006641097 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23172166231 / 1000000000000) (-23172164872 / 1000000000000), orderedInterval (48778869802 / 1000000000000) (48778871160 / 1000000000000)))) (orderedInterval (-3685727761 / 1000000000000) (-3685727466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (644322900415761 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-62697273681 / 1000000000000) (-62697273535 / 1000000000000), orderedInterval (4800207946 / 1000000000000) (4800208092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1104058271994453 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15986960595 / 1000000000000) (15986960596 / 1000000000000), orderedInterval (45257811240 / 1000000000000) (45257811241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (813244326128127 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6012627945 / 1000000000000) (6012627961 / 1000000000000), orderedInterval (-55648563641 / 1000000000000) (-55648563625 / 1000000000000)))) (orderedInterval (1655612795 / 1000000000000) (1655612821 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks2_1 :
    compactCertificate265.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1247725931444721 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-44806606540 / 1000000000000) (-44806605751 / 1000000000000), orderedInterval (5839115499 / 1000000000000) (5839116289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (720374902394409 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57795307902 / 1000000000000) (-57795306598 / 1000000000000), orderedInterval (14111306986 / 1000000000000) (14111308290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1278317905670781 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3476340617 / 1000000000000) (-3476340613 / 1000000000000), orderedInterval (44502316155 / 1000000000000) (44502316159 / 1000000000000)))) (orderedInterval (-30174411875 / 1000000000000) (-30174410760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1194370406515089 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36911261870 / 1000000000000) (-36911261869 / 1000000000000), orderedInterval (-27680326445 / 1000000000000) (-27680326444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (852359079261537 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13325691065 / 1000000000000) (13325691066 / 1000000000000), orderedInterval (52978158935 / 1000000000000) (52978158936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000)))) (orderedInterval (-6434453029 / 1000000000000) (-6434452983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (805753890490887 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51569579949 / 1000000000000) (51569579950 / 1000000000000), orderedInterval (22253689108 / 1000000000000) (22253689109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (711907998312627 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18192786710 / 1000000000000) (18192787045 / 1000000000000), orderedInterval (-57024891258 / 1000000000000) (-57024890923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (206338685858073 / 800000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (44223925694 / 1000000000000) (44223925695 / 1000000000000), orderedInterval (22552586917 / 1000000000000) (22552586918 / 1000000000000)))) (orderedInterval (-3458010630 / 1000000000000) (-3458010569 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks2_2 :
    compactCertificate265.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (570743664093531 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-57700116630 / 1000000000000) (-57700094277 / 1000000000000), orderedInterval (33852890463 / 1000000000000) (33852912817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (483825724865091 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51089185306 / 1000000000000) (51089249776 / 1000000000000), orderedInterval (-51719541305 / 1000000000000) (-51719476835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (302755673871873 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80643298190 / 1000000000000) (80643298191 / 1000000000000), orderedInterval (43142938835 / 1000000000000) (43142938836 / 1000000000000)))) (orderedInterval (-8234888394 / 1000000000000) (-8234881831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (162823008328191 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75419171902 / 1000000000000) (-75419171901 / 1000000000000), orderedInterval (-98832568829 / 1000000000000) (-98832568828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (442096141197573 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-74094197132 / 1000000000000) (-74094197131 / 1000000000000), orderedInterval (-16096749357 / 1000000000000) (-16096749355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (603644484843621 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50846428090 / 1000000000000) (50846428091 / 1000000000000), orderedInterval (40243707552 / 1000000000000) (40243707553 / 1000000000000)))) (orderedInterval (3404684425 / 1000000000000) (3404684441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (255244326128127 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98048643678 / 1000000000000) (98048644050 / 1000000000000), orderedInterval (-19815877677 / 1000000000000) (-19815877305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1037554014969567 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27098641119 / 1000000000000) (27098645932 / 1000000000000), orderedInterval (-41524822018 / 1000000000000) (-41524817204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (693037997530353 / 4000000000000) 2 (IntervalRat.scale (279 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-57648621075 / 1000000000000) (-57648621073 / 1000000000000), orderedInterval (-18568514187 / 1000000000000) (-18568514186 / 1000000000000)))) (orderedInterval (-9257797893 / 1000000000000) (-9257796451 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks2 :
    compactCertificate265.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate265.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate265_chunkChecks2_0
    compactCertificate265_chunkChecks2_1 compactCertificate265_chunkChecks2_2

theorem compactCertificate265_chunkChecks3_0 :
    compactCertificate265.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (279 / 2) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59806512935 / 1000000000000) (59806527361 / 1000000000000), orderedInterval (-31626878949 / 1000000000000) (-31626864523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (411020274464379 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10461704725 / 1000000000000) (10461704775 / 1000000000000), orderedInterval (-78064562153 / 1000000000000) (-78064562103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (132915511817307 / 800000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25501832533 / 1000000000000) (-25501832532 / 1000000000000), orderedInterval (-56327101770 / 1000000000000) (-56327101769 / 1000000000000)))) (orderedInterval (18563904422 / 1000000000000) (18563910196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (119934690989553 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88295803528 / 1000000000000) (-88295773888 / 1000000000000), orderedInterval (117389403889 / 1000000000000) (117389433530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (322161450207741 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31086064102 / 1000000000000) (-31086062997 / 1000000000000), orderedInterval (83488406130 / 1000000000000) (83488407235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (874731006641097 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23172166231 / 1000000000000) (-23172164872 / 1000000000000), orderedInterval (48778869802 / 1000000000000) (48778871160 / 1000000000000)))) (orderedInterval (12810758015 / 1000000000000) (12810758440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (644322900415761 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-62697273681 / 1000000000000) (-62697273535 / 1000000000000), orderedInterval (4800207946 / 1000000000000) (4800208092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1104058271994453 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15986960595 / 1000000000000) (15986960596 / 1000000000000), orderedInterval (45257811240 / 1000000000000) (45257811241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (813244326128127 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6012627945 / 1000000000000) (6012627961 / 1000000000000), orderedInterval (-55648563641 / 1000000000000) (-55648563625 / 1000000000000)))) (orderedInterval (14964148450 / 1000000000000) (14964148497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks3_1 :
    compactCertificate265.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1247725931444721 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-44806606540 / 1000000000000) (-44806605751 / 1000000000000), orderedInterval (5839115499 / 1000000000000) (5839116289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (720374902394409 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57795307902 / 1000000000000) (-57795306598 / 1000000000000), orderedInterval (14111306986 / 1000000000000) (14111308290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1278317905670781 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3476340617 / 1000000000000) (-3476340613 / 1000000000000), orderedInterval (44502316155 / 1000000000000) (44502316159 / 1000000000000)))) (orderedInterval (-66493481123 / 1000000000000) (-66493478794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1194370406515089 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36911261870 / 1000000000000) (-36911261869 / 1000000000000), orderedInterval (-27680326445 / 1000000000000) (-27680326444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (852359079261537 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13325691065 / 1000000000000) (13325691066 / 1000000000000), orderedInterval (52978158935 / 1000000000000) (52978158936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000)))) (orderedInterval (-23890817980 / 1000000000000) (-23890817903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (805753890490887 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51569579949 / 1000000000000) (51569579950 / 1000000000000), orderedInterval (22253689108 / 1000000000000) (22253689109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (711907998312627 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18192786710 / 1000000000000) (18192787045 / 1000000000000), orderedInterval (-57024891258 / 1000000000000) (-57024890923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (206338685858073 / 800000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (44223925694 / 1000000000000) (44223925695 / 1000000000000), orderedInterval (22552586917 / 1000000000000) (22552586918 / 1000000000000)))) (orderedInterval (-11175251523 / 1000000000000) (-11175251438 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks3_2 :
    compactCertificate265.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (570743664093531 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-57700116630 / 1000000000000) (-57700094277 / 1000000000000), orderedInterval (33852890463 / 1000000000000) (33852912817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (483825724865091 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51089185306 / 1000000000000) (51089249776 / 1000000000000), orderedInterval (-51719541305 / 1000000000000) (-51719476835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (302755673871873 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80643298190 / 1000000000000) (80643298191 / 1000000000000), orderedInterval (43142938835 / 1000000000000) (43142938836 / 1000000000000)))) (orderedInterval (3718539507 / 1000000000000) (3718545787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (162823008328191 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75419171902 / 1000000000000) (-75419171901 / 1000000000000), orderedInterval (-98832568829 / 1000000000000) (-98832568828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (442096141197573 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-74094197132 / 1000000000000) (-74094197131 / 1000000000000), orderedInterval (-16096749357 / 1000000000000) (-16096749355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (603644484843621 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50846428090 / 1000000000000) (50846428091 / 1000000000000), orderedInterval (40243707552 / 1000000000000) (40243707553 / 1000000000000)))) (orderedInterval (3653208951 / 1000000000000) (3653208967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (255244326128127 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98048643678 / 1000000000000) (98048644050 / 1000000000000), orderedInterval (-19815877677 / 1000000000000) (-19815877305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1037554014969567 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27098641119 / 1000000000000) (27098645932 / 1000000000000), orderedInterval (-41524822018 / 1000000000000) (-41524817204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (693037997530353 / 4000000000000) 3 (IntervalRat.scale (279 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-57648621075 / 1000000000000) (-57648621073 / 1000000000000), orderedInterval (-18568514187 / 1000000000000) (-18568514186 / 1000000000000)))) (orderedInterval (-28327060618 / 1000000000000) (-28327057964 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks3 :
    compactCertificate265.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate265.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate265_chunkChecks3_0
    compactCertificate265_chunkChecks3_1 compactCertificate265_chunkChecks3_2

theorem compactCertificate265_chunkChecks4_0 :
    compactCertificate265.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (279 / 2) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59806512935 / 1000000000000) (59806527361 / 1000000000000), orderedInterval (-31626878949 / 1000000000000) (-31626864523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (411020274464379 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10461704725 / 1000000000000) (10461704775 / 1000000000000), orderedInterval (-78064562153 / 1000000000000) (-78064562103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (132915511817307 / 800000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25501832533 / 1000000000000) (-25501832532 / 1000000000000), orderedInterval (-56327101770 / 1000000000000) (-56327101769 / 1000000000000)))) (orderedInterval (20455621937 / 1000000000000) (20455627754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (119934690989553 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88295803528 / 1000000000000) (-88295773888 / 1000000000000), orderedInterval (117389403889 / 1000000000000) (117389433530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (322161450207741 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31086064102 / 1000000000000) (-31086062997 / 1000000000000), orderedInterval (83488406130 / 1000000000000) (83488407235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (874731006641097 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23172166231 / 1000000000000) (-23172164872 / 1000000000000), orderedInterval (48778869802 / 1000000000000) (48778871160 / 1000000000000)))) (orderedInterval (9640042242 / 1000000000000) (9640042898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (644322900415761 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-62697273681 / 1000000000000) (-62697273535 / 1000000000000), orderedInterval (4800207946 / 1000000000000) (4800208092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1104058271994453 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15986960595 / 1000000000000) (15986960596 / 1000000000000), orderedInterval (45257811240 / 1000000000000) (45257811241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (813244326128127 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6012627945 / 1000000000000) (6012627961 / 1000000000000), orderedInterval (-55648563641 / 1000000000000) (-55648563625 / 1000000000000)))) (orderedInterval (-7116151734 / 1000000000000) (-7116151650 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks4_1 :
    compactCertificate265.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1247725931444721 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-44806606540 / 1000000000000) (-44806605751 / 1000000000000), orderedInterval (5839115499 / 1000000000000) (5839116289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (720374902394409 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-57795307902 / 1000000000000) (-57795306598 / 1000000000000), orderedInterval (14111306986 / 1000000000000) (14111308290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1278317905670781 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-3476340617 / 1000000000000) (-3476340613 / 1000000000000), orderedInterval (44502316155 / 1000000000000) (44502316159 / 1000000000000)))) (orderedInterval (174485200135 / 1000000000000) (174485205146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1194370406515089 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36911261870 / 1000000000000) (-36911261869 / 1000000000000), orderedInterval (-27680326445 / 1000000000000) (-27680326444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (852359079261537 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13325691065 / 1000000000000) (13325691066 / 1000000000000), orderedInterval (52978158935 / 1000000000000) (52978158936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000)))) (orderedInterval (22317634316 / 1000000000000) (22317634449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (805753890490887 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (51569579949 / 1000000000000) (51569579950 / 1000000000000), orderedInterval (22253689108 / 1000000000000) (22253689109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (711907998312627 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18192786710 / 1000000000000) (18192787045 / 1000000000000), orderedInterval (-57024891258 / 1000000000000) (-57024890923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (206338685858073 / 800000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (44223925694 / 1000000000000) (44223925695 / 1000000000000), orderedInterval (22552586917 / 1000000000000) (22552586918 / 1000000000000)))) (orderedInterval (13222956437 / 1000000000000) (13222956560 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks4_2 :
    compactCertificate265.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (570743664093531 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-57700116630 / 1000000000000) (-57700094277 / 1000000000000), orderedInterval (33852890463 / 1000000000000) (33852912817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (483825724865091 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51089185306 / 1000000000000) (51089249776 / 1000000000000), orderedInterval (-51719541305 / 1000000000000) (-51719476835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (302755673871873 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80643298190 / 1000000000000) (80643298191 / 1000000000000), orderedInterval (43142938835 / 1000000000000) (43142938836 / 1000000000000)))) (orderedInterval (8637285815 / 1000000000000) (8637291908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (162823008328191 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75419171902 / 1000000000000) (-75419171901 / 1000000000000), orderedInterval (-98832568829 / 1000000000000) (-98832568828 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (442096141197573 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-74094197132 / 1000000000000) (-74094197131 / 1000000000000), orderedInterval (-16096749357 / 1000000000000) (-16096749355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (603644484843621 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50846428090 / 1000000000000) (50846428091 / 1000000000000), orderedInterval (40243707552 / 1000000000000) (40243707553 / 1000000000000)))) (orderedInterval (-4716757869 / 1000000000000) (-4716757852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (255244326128127 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (98048643678 / 1000000000000) (98048644050 / 1000000000000), orderedInterval (-19815877677 / 1000000000000) (-19815877305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1037554014969567 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27098641119 / 1000000000000) (27098645932 / 1000000000000), orderedInterval (-41524822018 / 1000000000000) (-41524817204 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (693037997530353 / 4000000000000) 4 (IntervalRat.scale (279 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-57648621075 / 1000000000000) (-57648621073 / 1000000000000), orderedInterval (-18568514187 / 1000000000000) (-18568514186 / 1000000000000)))) (orderedInterval (-199122185 / 1000000000000) (-199117266 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate265_chunkChecks4 :
    compactCertificate265.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate265.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate265_chunkChecks4_0
    compactCertificate265_chunkChecks4_1 compactCertificate265_chunkChecks4_2

theorem compactCertificate265_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate265.chunkCheck r b = true :=
  compactCertificate265.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate265_chunkChecks0
    · exact compactCertificate265_chunkChecks1
    · exact compactCertificate265_chunkChecks2
    · exact compactCertificate265_chunkChecks3
    · exact compactCertificate265_chunkChecks4)

theorem compactCertificate265_coefficient0 :
    compactCertificate265.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate265, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate265_coefficient1 :
    compactCertificate265.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate265, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate265_coefficient2 :
    compactCertificate265.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate265, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate265_coefficient3 :
    compactCertificate265.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate265, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate265_coefficient4 :
    compactCertificate265.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate265, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate265_coefficients : ∀ r : Fin 5,
    compactCertificate265.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate265_coefficient0
  · exact compactCertificate265_coefficient1
  · exact compactCertificate265_coefficient2
  · exact compactCertificate265_coefficient3
  · exact compactCertificate265_coefficient4

theorem compactCertificate265_lower : (1 : ℚ) ≤ compactCertificate265.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate265, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate265_proves {t : ℝ} (ht : t ∈ compactCertificate265.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate265.proves compactCertificate265_states compactCertificate265_chunks
    compactCertificate265_coefficients compactCertificate265_lower ht

end Erdos232
