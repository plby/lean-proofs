/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate202 : CompactCertificate where
  left := 369 / 4
  right := 739 / 8
  center := 1477 / 16
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
    | 19 => 25
    | 20 => 16
    | 21 => 9
    | 22 => 23
    | 23 => 32
    | 24 => 13
    | 25 => 55
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 1477 / 16
    | 1 => 2175903030049777 / 32000000000000
    | 2 => 703642333169041 / 6400000000000
    | 3 => 634923077389139 / 32000000000000
    | 4 => 1705492695185783 / 32000000000000
    | 5 => 4630744433006811 / 32000000000000
    | 6 => 3410985390373043 / 32000000000000
    | 7 => 5844781604787839 / 32000000000000
    | 8 => 4305239676312701 / 32000000000000
    | 9 => 6605344805533523 / 32000000000000
    | 10 => 3813597601564667 / 32000000000000
    | 11 => 6767295866221303 / 32000000000000
    | 12 => 6322885628755507 / 32000000000000
    | 13 => 4512309534298531 / 32000000000000
    | 14 => 5116478085557349 / 32000000000000
    | 15 => 4265586008082581 / 32000000000000
    | 16 => 3768774600386201 / 32000000000000
    | 17 => 1092337774237899 / 6400000000000
    | 18 => 3021463770129553 / 32000000000000
    | 19 => 2561328299733833 / 32000000000000
    | 20 => 1602760323687299 / 32000000000000
    | 21 => 861969832619133 / 32000000000000
    | 22 => 2340415772576399 / 32000000000000
    | 23 => 3195637649154223 / 32000000000000
    | 24 => 1351239676312701 / 32000000000000
    | 25 => 5492714265627421 / 32000000000000
    | _ => 3668878574739539 / 32000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-75841137103 / 1000000000000) (-75841131106 / 1000000000000), orderedInterval (34239895964 / 1000000000000) (34239901961 / 1000000000000))
    | 1 => (orderedInterval (-31766328630 / 1000000000000) (-31766327723 / 1000000000000), orderedInterval (91631448379 / 1000000000000) (91631449286 / 1000000000000))
    | 2 => (orderedInterval (-53115538210 / 1000000000000) (-53115538209 / 1000000000000), orderedInterval (-54248221473 / 1000000000000) (-54248221472 / 1000000000000))
    | 3 => (orderedInterval (175522407439 / 1000000000000) (175522407766 / 1000000000000), orderedInterval (-40030116547 / 1000000000000) (-40030116219 / 1000000000000))
    | 4 => (orderedInterval (-68092201048 / 1000000000000) (-68092201047 / 1000000000000), orderedInterval (-84850473485 / 1000000000000) (-84850473484 / 1000000000000))
    | 5 => (orderedInterval (55159246154 / 1000000000000) (55159246155 / 1000000000000), orderedInterval (36642881374 / 1000000000000) (36642881375 / 1000000000000))
    | 6 => (orderedInterval (41270942676 / 1000000000000) (41270942677 / 1000000000000), orderedInterval (65145193391 / 1000000000000) (65145193392 / 1000000000000))
    | 7 => (orderedInterval (55478073724 / 1000000000000) (55478073725 / 1000000000000), orderedInterval (20038402110 / 1000000000000) (20038402111 / 1000000000000))
    | 8 => (orderedInterval (-15998478333 / 1000000000000) (-15998478332 / 1000000000000), orderedInterval (-66843065856 / 1000000000000) (-66843065855 / 1000000000000))
    | 9 => (orderedInterval (-7930809873 / 1000000000000) (-7930809846 / 1000000000000), orderedInterval (54985151394 / 1000000000000) (54985151421 / 1000000000000))
    | 10 => (orderedInterval (39977705184 / 1000000000000) (39977705185 / 1000000000000), orderedInterval (61018022605 / 1000000000000) (61018022606 / 1000000000000))
    | 11 => (orderedInterval (-53714261500 / 1000000000000) (-53714260416 / 1000000000000), orderedInterval (11312084698 / 1000000000000) (11312085782 / 1000000000000))
    | 12 => (orderedInterval (-24924523652 / 1000000000000) (-24924523651 / 1000000000000), orderedInterval (-50933935174 / 1000000000000) (-50933935173 / 1000000000000))
    | 13 => (orderedInterval (-27552259412 / 1000000000000) (-27552259411 / 1000000000000), orderedInterval (-61185385441 / 1000000000000) (-61185385440 / 1000000000000))
    | 14 => (orderedInterval (-27635388076 / 1000000000000) (-27635388075 / 1000000000000), orderedInterval (-56640203746 / 1000000000000) (-56640203745 / 1000000000000))
    | 15 => (orderedInterval (58317790474 / 1000000000000) (58317821007 / 1000000000000), orderedInterval (-37298094062 / 1000000000000) (-37298063529 / 1000000000000))
    | 16 => (orderedInterval (-53853907983 / 1000000000000) (-53853815572 / 1000000000000), orderedInterval (50280391191 / 1000000000000) (50280483603 / 1000000000000))
    | 17 => (orderedInterval (59239841858 / 1000000000000) (59239843225 / 1000000000000), orderedInterval (-15025413908 / 1000000000000) (-15025412541 / 1000000000000))
    | 18 => (orderedInterval (67125141572 / 1000000000000) (67125141573 / 1000000000000), orderedInterval (46936788037 / 1000000000000) (46936788038 / 1000000000000))
    | 19 => (orderedInterval (-67356511479 / 1000000000000) (-67356422343 / 1000000000000), orderedInterval (58873278600 / 1000000000000) (58873367737 / 1000000000000))
    | 20 => (orderedInterval (63998646980 / 1000000000000) (63998646981 / 1000000000000), orderedInterval (92177479169 / 1000000000000) (92177479170 / 1000000000000))
    | 21 => (orderedInterval (81265139027 / 1000000000000) (81265151300 / 1000000000000), orderedInterval (-132013926873 / 1000000000000) (-132013914600 / 1000000000000))
    | 22 => (orderedInterval (-92881983075 / 1000000000000) (-92881982969 / 1000000000000), orderedInterval (9415740126 / 1000000000000) (9415740232 / 1000000000000))
    | 23 => (orderedInterval (9309013402 / 1000000000000) (9309013404 / 1000000000000), orderedInterval (79252246152 / 1000000000000) (79252246154 / 1000000000000))
    | 24 => (orderedInterval (-101531373654 / 1000000000000) (-101531346643 / 1000000000000), orderedInterval (70248384839 / 1000000000000) (70248411849 / 1000000000000))
    | 25 => (orderedInterval (21202970740 / 1000000000000) (21202971368 / 1000000000000), orderedInterval (-57152292841 / 1000000000000) (-57152292214 / 1000000000000))
    | _ => (orderedInterval (53566328038 / 1000000000000) (53566407228 / 1000000000000), orderedInterval (-52033704392 / 1000000000000) (-52033625201 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-33473652671 / 1000000000000) (-33473650278 / 1000000000000)
      | 1 => orderedInterval (-8311709841 / 1000000000000) (-8311709825 / 1000000000000)
      | 2 => orderedInterval (-2097817421 / 1000000000000) (-2097817415 / 1000000000000)
      | 3 => orderedInterval (-3264570645 / 1000000000000) (-3264570448 / 1000000000000)
      | 4 => orderedInterval (-2015605070 / 1000000000000) (-2015605058 / 1000000000000)
      | 5 => orderedInterval (5272083453 / 1000000000000) (5272089138 / 1000000000000)
      | 6 => orderedInterval (-4836938981 / 1000000000000) (-4836933911 / 1000000000000)
      | 7 => orderedInterval (-106802071 / 1000000000000) (-106801830 / 1000000000000)
      | _ => orderedInterval (-12388502935 / 1000000000000) (-12388487836 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (10409057138 / 1000000000000) (10409059529 / 1000000000000)
      | 1 => orderedInterval (-5778841741 / 1000000000000) (-5778841726 / 1000000000000)
      | 2 => orderedInterval (-3577324342 / 1000000000000) (-3577324332 / 1000000000000)
      | 3 => orderedInterval (-12326389042 / 1000000000000) (-12326388602 / 1000000000000)
      | 4 => orderedInterval (-6373419996 / 1000000000000) (-6373419977 / 1000000000000)
      | 5 => orderedInterval (-5004263836 / 1000000000000) (-5004256502 / 1000000000000)
      | 6 => orderedInterval (-8937327801 / 1000000000000) (-8937323404 / 1000000000000)
      | 7 => orderedInterval (-6028582962 / 1000000000000) (-6028582883 / 1000000000000)
      | _ => orderedInterval (20969810341 / 1000000000000) (20969829002 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (34529841996 / 1000000000000) (34529844413 / 1000000000000)
      | 1 => orderedInterval (10615485254 / 1000000000000) (10615485273 / 1000000000000)
      | 2 => orderedInterval (7559001191 / 1000000000000) (7559001208 / 1000000000000)
      | 3 => orderedInterval (28224887907 / 1000000000000) (28224888907 / 1000000000000)
      | 4 => orderedInterval (3667281526 / 1000000000000) (3667281556 / 1000000000000)
      | 5 => orderedInterval (-11551494253 / 1000000000000) (-11551484691 / 1000000000000)
      | 6 => orderedInterval (7845909252 / 1000000000000) (7845913113 / 1000000000000)
      | 7 => orderedInterval (-294732010 / 1000000000000) (-294731978 / 1000000000000)
      | _ => orderedInterval (21371859327 / 1000000000000) (21371882713 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8907597563 / 1000000000000) (-8907595147 / 1000000000000)
      | 1 => orderedInterval (10511221296 / 1000000000000) (10511221323 / 1000000000000)
      | 2 => orderedInterval (9706191838 / 1000000000000) (9706191869 / 1000000000000)
      | 3 => orderedInterval (79865435025 / 1000000000000) (79865437297 / 1000000000000)
      | 4 => orderedInterval (10075039802 / 1000000000000) (10075039854 / 1000000000000)
      | 5 => orderedInterval (9828320747 / 1000000000000) (9828333144 / 1000000000000)
      | 6 => orderedInterval (9637696817 / 1000000000000) (9637700167 / 1000000000000)
      | 7 => orderedInterval (7737723454 / 1000000000000) (7737723472 / 1000000000000)
      | _ => orderedInterval (-48882818823 / 1000000000000) (-48882789683 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-36222305314 / 1000000000000) (-36222302872 / 1000000000000)
      | 1 => orderedInterval (-24187013898 / 1000000000000) (-24187013856 / 1000000000000)
      | 2 => orderedInterval (-28179352732 / 1000000000000) (-28179352677 / 1000000000000)
      | 3 => orderedInterval (-168585354366 / 1000000000000) (-168585349168 / 1000000000000)
      | 4 => orderedInterval (-3699345300 / 1000000000000) (-3699345211 / 1000000000000)
      | 5 => orderedInterval (28604044603 / 1000000000000) (28604060866 / 1000000000000)
      | 6 => orderedInterval (-9619849907 / 1000000000000) (-9619846965 / 1000000000000)
      | 7 => orderedInterval (-325350106 / 1000000000000) (-325350091 / 1000000000000)
      | _ => orderedInterval (-43512450268 / 1000000000000) (-43512413546 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-61223516182 / 1000000000000) (-61223487463 / 1000000000000)
    | 1 => orderedInterval (-16647282241 / 1000000000000) (-16647248895 / 1000000000000)
    | 2 => orderedInterval (101968040190 / 1000000000000) (101968080514 / 1000000000000)
    | 3 => orderedInterval (79571212593 / 1000000000000) (79571262296 / 1000000000000)
    | _ => orderedInterval (-285726977288 / 1000000000000) (-285726913520 / 1000000000000)

theorem compactCertificate202_stateChecks0 :
    compactCertificate202.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (1477 / 16)) (orderedInterval (-75841137103 / 1000000000000) (-75841131106 / 1000000000000), orderedInterval (34239895964 / 1000000000000) (34239901961 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (2175903030049777 / 32000000000000)) (orderedInterval (-31766328630 / 1000000000000) (-31766327723 / 1000000000000), orderedInterval (91631448379 / 1000000000000) (91631449286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (703642333169041 / 6400000000000)) (orderedInterval (-53115538210 / 1000000000000) (-53115538209 / 1000000000000), orderedInterval (-54248221473 / 1000000000000) (-54248221472 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_stateChecks1 :
    compactCertificate202.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (634923077389139 / 32000000000000)) (orderedInterval (175522407439 / 1000000000000) (175522407766 / 1000000000000), orderedInterval (-40030116547 / 1000000000000) (-40030116219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (1705492695185783 / 32000000000000)) (orderedInterval (-68092201048 / 1000000000000) (-68092201047 / 1000000000000), orderedInterval (-84850473485 / 1000000000000) (-84850473484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (4630744433006811 / 32000000000000)) (orderedInterval (55159246154 / 1000000000000) (55159246155 / 1000000000000), orderedInterval (36642881374 / 1000000000000) (36642881375 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_stateChecks2 :
    compactCertificate202.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (3410985390373043 / 32000000000000)) (orderedInterval (41270942676 / 1000000000000) (41270942677 / 1000000000000), orderedInterval (65145193391 / 1000000000000) (65145193392 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (5844781604787839 / 32000000000000)) (orderedInterval (55478073724 / 1000000000000) (55478073725 / 1000000000000), orderedInterval (20038402110 / 1000000000000) (20038402111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (4305239676312701 / 32000000000000)) (orderedInterval (-15998478333 / 1000000000000) (-15998478332 / 1000000000000), orderedInterval (-66843065856 / 1000000000000) (-66843065855 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_stateChecks3 :
    compactCertificate202.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (6605344805533523 / 32000000000000)) (orderedInterval (-7930809873 / 1000000000000) (-7930809846 / 1000000000000), orderedInterval (54985151394 / 1000000000000) (54985151421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (3813597601564667 / 32000000000000)) (orderedInterval (39977705184 / 1000000000000) (39977705185 / 1000000000000), orderedInterval (61018022605 / 1000000000000) (61018022606 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (6767295866221303 / 32000000000000)) (orderedInterval (-53714261500 / 1000000000000) (-53714260416 / 1000000000000), orderedInterval (11312084698 / 1000000000000) (11312085782 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_stateChecks4 :
    compactCertificate202.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (6322885628755507 / 32000000000000)) (orderedInterval (-24924523652 / 1000000000000) (-24924523651 / 1000000000000), orderedInterval (-50933935174 / 1000000000000) (-50933935173 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (4512309534298531 / 32000000000000)) (orderedInterval (-27552259412 / 1000000000000) (-27552259411 / 1000000000000), orderedInterval (-61185385441 / 1000000000000) (-61185385440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (5116478085557349 / 32000000000000)) (orderedInterval (-27635388076 / 1000000000000) (-27635388075 / 1000000000000), orderedInterval (-56640203746 / 1000000000000) (-56640203745 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_stateChecks5 :
    compactCertificate202.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (4265586008082581 / 32000000000000)) (orderedInterval (58317790474 / 1000000000000) (58317821007 / 1000000000000), orderedInterval (-37298094062 / 1000000000000) (-37298063529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (3768774600386201 / 32000000000000)) (orderedInterval (-53853907983 / 1000000000000) (-53853815572 / 1000000000000), orderedInterval (50280391191 / 1000000000000) (50280483603 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1092337774237899 / 6400000000000)) (orderedInterval (59239841858 / 1000000000000) (59239843225 / 1000000000000), orderedInterval (-15025413908 / 1000000000000) (-15025412541 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_stateChecks6 :
    compactCertificate202.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (3021463770129553 / 32000000000000)) (orderedInterval (67125141572 / 1000000000000) (67125141573 / 1000000000000), orderedInterval (46936788037 / 1000000000000) (46936788038 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (2561328299733833 / 32000000000000)) (orderedInterval (-67356511479 / 1000000000000) (-67356422343 / 1000000000000), orderedInterval (58873278600 / 1000000000000) (58873367737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (1602760323687299 / 32000000000000)) (orderedInterval (63998646980 / 1000000000000) (63998646981 / 1000000000000), orderedInterval (92177479169 / 1000000000000) (92177479170 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_stateChecks7 :
    compactCertificate202.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (861969832619133 / 32000000000000)) (orderedInterval (81265139027 / 1000000000000) (81265151300 / 1000000000000), orderedInterval (-132013926873 / 1000000000000) (-132013914600 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (2340415772576399 / 32000000000000)) (orderedInterval (-92881983075 / 1000000000000) (-92881982969 / 1000000000000), orderedInterval (9415740126 / 1000000000000) (9415740232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (3195637649154223 / 32000000000000)) (orderedInterval (9309013402 / 1000000000000) (9309013404 / 1000000000000), orderedInterval (79252246152 / 1000000000000) (79252246154 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_stateChecks8 :
    compactCertificate202.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (1351239676312701 / 32000000000000)) (orderedInterval (-101531373654 / 1000000000000) (-101531346643 / 1000000000000), orderedInterval (70248384839 / 1000000000000) (70248411849 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (5492714265627421 / 32000000000000)) (orderedInterval (21202970740 / 1000000000000) (21202971368 / 1000000000000), orderedInterval (-57152292841 / 1000000000000) (-57152292214 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (3668878574739539 / 32000000000000)) (orderedInterval (53566328038 / 1000000000000) (53566407228 / 1000000000000), orderedInterval (-52033704392 / 1000000000000) (-52033625201 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState025, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState042, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate202_states : ∀ j,
    BesselStateValid (compactCertificate202.point j) (compactCertificate202.state j) :=
  compactCertificate202.statesValid_of_checks3 compactCertificate202_stateChecks0
    compactCertificate202_stateChecks1 compactCertificate202_stateChecks2
    compactCertificate202_stateChecks3 compactCertificate202_stateChecks4
    compactCertificate202_stateChecks5 compactCertificate202_stateChecks6
    compactCertificate202_stateChecks7 compactCertificate202_stateChecks8

theorem compactCertificate202_chunkChecks0_0 :
    compactCertificate202.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (1477 / 16) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-75841137103 / 1000000000000) (-75841131106 / 1000000000000), orderedInterval (34239895964 / 1000000000000) (34239901961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (2175903030049777 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31766328630 / 1000000000000) (-31766327723 / 1000000000000), orderedInterval (91631448379 / 1000000000000) (91631449286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (703642333169041 / 6400000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53115538210 / 1000000000000) (-53115538209 / 1000000000000), orderedInterval (-54248221473 / 1000000000000) (-54248221472 / 1000000000000)))) (orderedInterval (-33473652671 / 1000000000000) (-33473650278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (634923077389139 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (175522407439 / 1000000000000) (175522407766 / 1000000000000), orderedInterval (-40030116547 / 1000000000000) (-40030116219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1705492695185783 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68092201048 / 1000000000000) (-68092201047 / 1000000000000), orderedInterval (-84850473485 / 1000000000000) (-84850473484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (4630744433006811 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (55159246154 / 1000000000000) (55159246155 / 1000000000000), orderedInterval (36642881374 / 1000000000000) (36642881375 / 1000000000000)))) (orderedInterval (-8311709841 / 1000000000000) (-8311709825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (3410985390373043 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41270942676 / 1000000000000) (41270942677 / 1000000000000), orderedInterval (65145193391 / 1000000000000) (65145193392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (5844781604787839 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (55478073724 / 1000000000000) (55478073725 / 1000000000000), orderedInterval (20038402110 / 1000000000000) (20038402111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (4305239676312701 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15998478333 / 1000000000000) (-15998478332 / 1000000000000), orderedInterval (-66843065856 / 1000000000000) (-66843065855 / 1000000000000)))) (orderedInterval (-2097817421 / 1000000000000) (-2097817415 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks0_1 :
    compactCertificate202.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (6605344805533523 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7930809873 / 1000000000000) (-7930809846 / 1000000000000), orderedInterval (54985151394 / 1000000000000) (54985151421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (3813597601564667 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39977705184 / 1000000000000) (39977705185 / 1000000000000), orderedInterval (61018022605 / 1000000000000) (61018022606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (6767295866221303 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53714261500 / 1000000000000) (-53714260416 / 1000000000000), orderedInterval (11312084698 / 1000000000000) (11312085782 / 1000000000000)))) (orderedInterval (-3264570645 / 1000000000000) (-3264570448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (6322885628755507 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24924523652 / 1000000000000) (-24924523651 / 1000000000000), orderedInterval (-50933935174 / 1000000000000) (-50933935173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (4512309534298531 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27552259412 / 1000000000000) (-27552259411 / 1000000000000), orderedInterval (-61185385441 / 1000000000000) (-61185385440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (5116478085557349 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27635388076 / 1000000000000) (-27635388075 / 1000000000000), orderedInterval (-56640203746 / 1000000000000) (-56640203745 / 1000000000000)))) (orderedInterval (-2015605070 / 1000000000000) (-2015605058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (4265586008082581 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (58317790474 / 1000000000000) (58317821007 / 1000000000000), orderedInterval (-37298094062 / 1000000000000) (-37298063529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (3768774600386201 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53853907983 / 1000000000000) (-53853815572 / 1000000000000), orderedInterval (50280391191 / 1000000000000) (50280483603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (1092337774237899 / 6400000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59239841858 / 1000000000000) (59239843225 / 1000000000000), orderedInterval (-15025413908 / 1000000000000) (-15025412541 / 1000000000000)))) (orderedInterval (5272083453 / 1000000000000) (5272089138 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks0_2 :
    compactCertificate202.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (3021463770129553 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67125141572 / 1000000000000) (67125141573 / 1000000000000), orderedInterval (46936788037 / 1000000000000) (46936788038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (2561328299733833 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67356511479 / 1000000000000) (-67356422343 / 1000000000000), orderedInterval (58873278600 / 1000000000000) (58873367737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1602760323687299 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (63998646980 / 1000000000000) (63998646981 / 1000000000000), orderedInterval (92177479169 / 1000000000000) (92177479170 / 1000000000000)))) (orderedInterval (-4836938981 / 1000000000000) (-4836933911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (861969832619133 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81265139027 / 1000000000000) (81265151300 / 1000000000000), orderedInterval (-132013926873 / 1000000000000) (-132013914600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (2340415772576399 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92881983075 / 1000000000000) (-92881982969 / 1000000000000), orderedInterval (9415740126 / 1000000000000) (9415740232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (3195637649154223 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9309013402 / 1000000000000) (9309013404 / 1000000000000), orderedInterval (79252246152 / 1000000000000) (79252246154 / 1000000000000)))) (orderedInterval (-106802071 / 1000000000000) (-106801830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (1351239676312701 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101531373654 / 1000000000000) (-101531346643 / 1000000000000), orderedInterval (70248384839 / 1000000000000) (70248411849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (5492714265627421 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202970740 / 1000000000000) (21202971368 / 1000000000000), orderedInterval (-57152292841 / 1000000000000) (-57152292214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (3668878574739539 / 32000000000000) 0 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53566328038 / 1000000000000) (53566407228 / 1000000000000), orderedInterval (-52033704392 / 1000000000000) (-52033625201 / 1000000000000)))) (orderedInterval (-12388502935 / 1000000000000) (-12388487836 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks0 :
    compactCertificate202.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate202.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate202_chunkChecks0_0
    compactCertificate202_chunkChecks0_1 compactCertificate202_chunkChecks0_2

theorem compactCertificate202_chunkChecks1_0 :
    compactCertificate202.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (1477 / 16) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-75841137103 / 1000000000000) (-75841131106 / 1000000000000), orderedInterval (34239895964 / 1000000000000) (34239901961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (2175903030049777 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31766328630 / 1000000000000) (-31766327723 / 1000000000000), orderedInterval (91631448379 / 1000000000000) (91631449286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (703642333169041 / 6400000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53115538210 / 1000000000000) (-53115538209 / 1000000000000), orderedInterval (-54248221473 / 1000000000000) (-54248221472 / 1000000000000)))) (orderedInterval (10409057138 / 1000000000000) (10409059529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (634923077389139 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (175522407439 / 1000000000000) (175522407766 / 1000000000000), orderedInterval (-40030116547 / 1000000000000) (-40030116219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1705492695185783 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68092201048 / 1000000000000) (-68092201047 / 1000000000000), orderedInterval (-84850473485 / 1000000000000) (-84850473484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (4630744433006811 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (55159246154 / 1000000000000) (55159246155 / 1000000000000), orderedInterval (36642881374 / 1000000000000) (36642881375 / 1000000000000)))) (orderedInterval (-5778841741 / 1000000000000) (-5778841726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (3410985390373043 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41270942676 / 1000000000000) (41270942677 / 1000000000000), orderedInterval (65145193391 / 1000000000000) (65145193392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (5844781604787839 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (55478073724 / 1000000000000) (55478073725 / 1000000000000), orderedInterval (20038402110 / 1000000000000) (20038402111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (4305239676312701 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15998478333 / 1000000000000) (-15998478332 / 1000000000000), orderedInterval (-66843065856 / 1000000000000) (-66843065855 / 1000000000000)))) (orderedInterval (-3577324342 / 1000000000000) (-3577324332 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks1_1 :
    compactCertificate202.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (6605344805533523 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7930809873 / 1000000000000) (-7930809846 / 1000000000000), orderedInterval (54985151394 / 1000000000000) (54985151421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (3813597601564667 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39977705184 / 1000000000000) (39977705185 / 1000000000000), orderedInterval (61018022605 / 1000000000000) (61018022606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (6767295866221303 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53714261500 / 1000000000000) (-53714260416 / 1000000000000), orderedInterval (11312084698 / 1000000000000) (11312085782 / 1000000000000)))) (orderedInterval (-12326389042 / 1000000000000) (-12326388602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (6322885628755507 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24924523652 / 1000000000000) (-24924523651 / 1000000000000), orderedInterval (-50933935174 / 1000000000000) (-50933935173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (4512309534298531 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27552259412 / 1000000000000) (-27552259411 / 1000000000000), orderedInterval (-61185385441 / 1000000000000) (-61185385440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (5116478085557349 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27635388076 / 1000000000000) (-27635388075 / 1000000000000), orderedInterval (-56640203746 / 1000000000000) (-56640203745 / 1000000000000)))) (orderedInterval (-6373419996 / 1000000000000) (-6373419977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (4265586008082581 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (58317790474 / 1000000000000) (58317821007 / 1000000000000), orderedInterval (-37298094062 / 1000000000000) (-37298063529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (3768774600386201 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53853907983 / 1000000000000) (-53853815572 / 1000000000000), orderedInterval (50280391191 / 1000000000000) (50280483603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (1092337774237899 / 6400000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59239841858 / 1000000000000) (59239843225 / 1000000000000), orderedInterval (-15025413908 / 1000000000000) (-15025412541 / 1000000000000)))) (orderedInterval (-5004263836 / 1000000000000) (-5004256502 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks1_2 :
    compactCertificate202.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (3021463770129553 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67125141572 / 1000000000000) (67125141573 / 1000000000000), orderedInterval (46936788037 / 1000000000000) (46936788038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (2561328299733833 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67356511479 / 1000000000000) (-67356422343 / 1000000000000), orderedInterval (58873278600 / 1000000000000) (58873367737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1602760323687299 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (63998646980 / 1000000000000) (63998646981 / 1000000000000), orderedInterval (92177479169 / 1000000000000) (92177479170 / 1000000000000)))) (orderedInterval (-8937327801 / 1000000000000) (-8937323404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (861969832619133 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81265139027 / 1000000000000) (81265151300 / 1000000000000), orderedInterval (-132013926873 / 1000000000000) (-132013914600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (2340415772576399 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92881983075 / 1000000000000) (-92881982969 / 1000000000000), orderedInterval (9415740126 / 1000000000000) (9415740232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (3195637649154223 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9309013402 / 1000000000000) (9309013404 / 1000000000000), orderedInterval (79252246152 / 1000000000000) (79252246154 / 1000000000000)))) (orderedInterval (-6028582962 / 1000000000000) (-6028582883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (1351239676312701 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101531373654 / 1000000000000) (-101531346643 / 1000000000000), orderedInterval (70248384839 / 1000000000000) (70248411849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (5492714265627421 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202970740 / 1000000000000) (21202971368 / 1000000000000), orderedInterval (-57152292841 / 1000000000000) (-57152292214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (3668878574739539 / 32000000000000) 1 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53566328038 / 1000000000000) (53566407228 / 1000000000000), orderedInterval (-52033704392 / 1000000000000) (-52033625201 / 1000000000000)))) (orderedInterval (20969810341 / 1000000000000) (20969829002 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks1 :
    compactCertificate202.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate202.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate202_chunkChecks1_0
    compactCertificate202_chunkChecks1_1 compactCertificate202_chunkChecks1_2

theorem compactCertificate202_chunkChecks2_0 :
    compactCertificate202.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (1477 / 16) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-75841137103 / 1000000000000) (-75841131106 / 1000000000000), orderedInterval (34239895964 / 1000000000000) (34239901961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (2175903030049777 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31766328630 / 1000000000000) (-31766327723 / 1000000000000), orderedInterval (91631448379 / 1000000000000) (91631449286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (703642333169041 / 6400000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53115538210 / 1000000000000) (-53115538209 / 1000000000000), orderedInterval (-54248221473 / 1000000000000) (-54248221472 / 1000000000000)))) (orderedInterval (34529841996 / 1000000000000) (34529844413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (634923077389139 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (175522407439 / 1000000000000) (175522407766 / 1000000000000), orderedInterval (-40030116547 / 1000000000000) (-40030116219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1705492695185783 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68092201048 / 1000000000000) (-68092201047 / 1000000000000), orderedInterval (-84850473485 / 1000000000000) (-84850473484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (4630744433006811 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (55159246154 / 1000000000000) (55159246155 / 1000000000000), orderedInterval (36642881374 / 1000000000000) (36642881375 / 1000000000000)))) (orderedInterval (10615485254 / 1000000000000) (10615485273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (3410985390373043 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41270942676 / 1000000000000) (41270942677 / 1000000000000), orderedInterval (65145193391 / 1000000000000) (65145193392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (5844781604787839 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (55478073724 / 1000000000000) (55478073725 / 1000000000000), orderedInterval (20038402110 / 1000000000000) (20038402111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (4305239676312701 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15998478333 / 1000000000000) (-15998478332 / 1000000000000), orderedInterval (-66843065856 / 1000000000000) (-66843065855 / 1000000000000)))) (orderedInterval (7559001191 / 1000000000000) (7559001208 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks2_1 :
    compactCertificate202.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (6605344805533523 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7930809873 / 1000000000000) (-7930809846 / 1000000000000), orderedInterval (54985151394 / 1000000000000) (54985151421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (3813597601564667 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39977705184 / 1000000000000) (39977705185 / 1000000000000), orderedInterval (61018022605 / 1000000000000) (61018022606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (6767295866221303 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53714261500 / 1000000000000) (-53714260416 / 1000000000000), orderedInterval (11312084698 / 1000000000000) (11312085782 / 1000000000000)))) (orderedInterval (28224887907 / 1000000000000) (28224888907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (6322885628755507 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24924523652 / 1000000000000) (-24924523651 / 1000000000000), orderedInterval (-50933935174 / 1000000000000) (-50933935173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (4512309534298531 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27552259412 / 1000000000000) (-27552259411 / 1000000000000), orderedInterval (-61185385441 / 1000000000000) (-61185385440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (5116478085557349 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27635388076 / 1000000000000) (-27635388075 / 1000000000000), orderedInterval (-56640203746 / 1000000000000) (-56640203745 / 1000000000000)))) (orderedInterval (3667281526 / 1000000000000) (3667281556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (4265586008082581 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (58317790474 / 1000000000000) (58317821007 / 1000000000000), orderedInterval (-37298094062 / 1000000000000) (-37298063529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (3768774600386201 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53853907983 / 1000000000000) (-53853815572 / 1000000000000), orderedInterval (50280391191 / 1000000000000) (50280483603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (1092337774237899 / 6400000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59239841858 / 1000000000000) (59239843225 / 1000000000000), orderedInterval (-15025413908 / 1000000000000) (-15025412541 / 1000000000000)))) (orderedInterval (-11551494253 / 1000000000000) (-11551484691 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks2_2 :
    compactCertificate202.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (3021463770129553 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67125141572 / 1000000000000) (67125141573 / 1000000000000), orderedInterval (46936788037 / 1000000000000) (46936788038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (2561328299733833 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67356511479 / 1000000000000) (-67356422343 / 1000000000000), orderedInterval (58873278600 / 1000000000000) (58873367737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1602760323687299 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (63998646980 / 1000000000000) (63998646981 / 1000000000000), orderedInterval (92177479169 / 1000000000000) (92177479170 / 1000000000000)))) (orderedInterval (7845909252 / 1000000000000) (7845913113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (861969832619133 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81265139027 / 1000000000000) (81265151300 / 1000000000000), orderedInterval (-132013926873 / 1000000000000) (-132013914600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (2340415772576399 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92881983075 / 1000000000000) (-92881982969 / 1000000000000), orderedInterval (9415740126 / 1000000000000) (9415740232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (3195637649154223 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9309013402 / 1000000000000) (9309013404 / 1000000000000), orderedInterval (79252246152 / 1000000000000) (79252246154 / 1000000000000)))) (orderedInterval (-294732010 / 1000000000000) (-294731978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (1351239676312701 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101531373654 / 1000000000000) (-101531346643 / 1000000000000), orderedInterval (70248384839 / 1000000000000) (70248411849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (5492714265627421 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202970740 / 1000000000000) (21202971368 / 1000000000000), orderedInterval (-57152292841 / 1000000000000) (-57152292214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (3668878574739539 / 32000000000000) 2 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53566328038 / 1000000000000) (53566407228 / 1000000000000), orderedInterval (-52033704392 / 1000000000000) (-52033625201 / 1000000000000)))) (orderedInterval (21371859327 / 1000000000000) (21371882713 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks2 :
    compactCertificate202.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate202.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate202_chunkChecks2_0
    compactCertificate202_chunkChecks2_1 compactCertificate202_chunkChecks2_2

theorem compactCertificate202_chunkChecks3_0 :
    compactCertificate202.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (1477 / 16) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-75841137103 / 1000000000000) (-75841131106 / 1000000000000), orderedInterval (34239895964 / 1000000000000) (34239901961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (2175903030049777 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31766328630 / 1000000000000) (-31766327723 / 1000000000000), orderedInterval (91631448379 / 1000000000000) (91631449286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (703642333169041 / 6400000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53115538210 / 1000000000000) (-53115538209 / 1000000000000), orderedInterval (-54248221473 / 1000000000000) (-54248221472 / 1000000000000)))) (orderedInterval (-8907597563 / 1000000000000) (-8907595147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (634923077389139 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (175522407439 / 1000000000000) (175522407766 / 1000000000000), orderedInterval (-40030116547 / 1000000000000) (-40030116219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1705492695185783 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68092201048 / 1000000000000) (-68092201047 / 1000000000000), orderedInterval (-84850473485 / 1000000000000) (-84850473484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (4630744433006811 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (55159246154 / 1000000000000) (55159246155 / 1000000000000), orderedInterval (36642881374 / 1000000000000) (36642881375 / 1000000000000)))) (orderedInterval (10511221296 / 1000000000000) (10511221323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (3410985390373043 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41270942676 / 1000000000000) (41270942677 / 1000000000000), orderedInterval (65145193391 / 1000000000000) (65145193392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (5844781604787839 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (55478073724 / 1000000000000) (55478073725 / 1000000000000), orderedInterval (20038402110 / 1000000000000) (20038402111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (4305239676312701 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15998478333 / 1000000000000) (-15998478332 / 1000000000000), orderedInterval (-66843065856 / 1000000000000) (-66843065855 / 1000000000000)))) (orderedInterval (9706191838 / 1000000000000) (9706191869 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks3_1 :
    compactCertificate202.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (6605344805533523 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7930809873 / 1000000000000) (-7930809846 / 1000000000000), orderedInterval (54985151394 / 1000000000000) (54985151421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (3813597601564667 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39977705184 / 1000000000000) (39977705185 / 1000000000000), orderedInterval (61018022605 / 1000000000000) (61018022606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (6767295866221303 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53714261500 / 1000000000000) (-53714260416 / 1000000000000), orderedInterval (11312084698 / 1000000000000) (11312085782 / 1000000000000)))) (orderedInterval (79865435025 / 1000000000000) (79865437297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (6322885628755507 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24924523652 / 1000000000000) (-24924523651 / 1000000000000), orderedInterval (-50933935174 / 1000000000000) (-50933935173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (4512309534298531 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27552259412 / 1000000000000) (-27552259411 / 1000000000000), orderedInterval (-61185385441 / 1000000000000) (-61185385440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (5116478085557349 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27635388076 / 1000000000000) (-27635388075 / 1000000000000), orderedInterval (-56640203746 / 1000000000000) (-56640203745 / 1000000000000)))) (orderedInterval (10075039802 / 1000000000000) (10075039854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (4265586008082581 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (58317790474 / 1000000000000) (58317821007 / 1000000000000), orderedInterval (-37298094062 / 1000000000000) (-37298063529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (3768774600386201 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53853907983 / 1000000000000) (-53853815572 / 1000000000000), orderedInterval (50280391191 / 1000000000000) (50280483603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (1092337774237899 / 6400000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59239841858 / 1000000000000) (59239843225 / 1000000000000), orderedInterval (-15025413908 / 1000000000000) (-15025412541 / 1000000000000)))) (orderedInterval (9828320747 / 1000000000000) (9828333144 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks3_2 :
    compactCertificate202.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (3021463770129553 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67125141572 / 1000000000000) (67125141573 / 1000000000000), orderedInterval (46936788037 / 1000000000000) (46936788038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (2561328299733833 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67356511479 / 1000000000000) (-67356422343 / 1000000000000), orderedInterval (58873278600 / 1000000000000) (58873367737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1602760323687299 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (63998646980 / 1000000000000) (63998646981 / 1000000000000), orderedInterval (92177479169 / 1000000000000) (92177479170 / 1000000000000)))) (orderedInterval (9637696817 / 1000000000000) (9637700167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (861969832619133 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81265139027 / 1000000000000) (81265151300 / 1000000000000), orderedInterval (-132013926873 / 1000000000000) (-132013914600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (2340415772576399 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92881983075 / 1000000000000) (-92881982969 / 1000000000000), orderedInterval (9415740126 / 1000000000000) (9415740232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (3195637649154223 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9309013402 / 1000000000000) (9309013404 / 1000000000000), orderedInterval (79252246152 / 1000000000000) (79252246154 / 1000000000000)))) (orderedInterval (7737723454 / 1000000000000) (7737723472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (1351239676312701 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101531373654 / 1000000000000) (-101531346643 / 1000000000000), orderedInterval (70248384839 / 1000000000000) (70248411849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (5492714265627421 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202970740 / 1000000000000) (21202971368 / 1000000000000), orderedInterval (-57152292841 / 1000000000000) (-57152292214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (3668878574739539 / 32000000000000) 3 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53566328038 / 1000000000000) (53566407228 / 1000000000000), orderedInterval (-52033704392 / 1000000000000) (-52033625201 / 1000000000000)))) (orderedInterval (-48882818823 / 1000000000000) (-48882789683 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks3 :
    compactCertificate202.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate202.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate202_chunkChecks3_0
    compactCertificate202_chunkChecks3_1 compactCertificate202_chunkChecks3_2

theorem compactCertificate202_chunkChecks4_0 :
    compactCertificate202.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (1477 / 16) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-75841137103 / 1000000000000) (-75841131106 / 1000000000000), orderedInterval (34239895964 / 1000000000000) (34239901961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (2175903030049777 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31766328630 / 1000000000000) (-31766327723 / 1000000000000), orderedInterval (91631448379 / 1000000000000) (91631449286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (703642333169041 / 6400000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53115538210 / 1000000000000) (-53115538209 / 1000000000000), orderedInterval (-54248221473 / 1000000000000) (-54248221472 / 1000000000000)))) (orderedInterval (-36222305314 / 1000000000000) (-36222302872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (634923077389139 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (175522407439 / 1000000000000) (175522407766 / 1000000000000), orderedInterval (-40030116547 / 1000000000000) (-40030116219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1705492695185783 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68092201048 / 1000000000000) (-68092201047 / 1000000000000), orderedInterval (-84850473485 / 1000000000000) (-84850473484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (4630744433006811 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (55159246154 / 1000000000000) (55159246155 / 1000000000000), orderedInterval (36642881374 / 1000000000000) (36642881375 / 1000000000000)))) (orderedInterval (-24187013898 / 1000000000000) (-24187013856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (3410985390373043 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41270942676 / 1000000000000) (41270942677 / 1000000000000), orderedInterval (65145193391 / 1000000000000) (65145193392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (5844781604787839 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (55478073724 / 1000000000000) (55478073725 / 1000000000000), orderedInterval (20038402110 / 1000000000000) (20038402111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (4305239676312701 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15998478333 / 1000000000000) (-15998478332 / 1000000000000), orderedInterval (-66843065856 / 1000000000000) (-66843065855 / 1000000000000)))) (orderedInterval (-28179352732 / 1000000000000) (-28179352677 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks4_1 :
    compactCertificate202.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (6605344805533523 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7930809873 / 1000000000000) (-7930809846 / 1000000000000), orderedInterval (54985151394 / 1000000000000) (54985151421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (3813597601564667 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39977705184 / 1000000000000) (39977705185 / 1000000000000), orderedInterval (61018022605 / 1000000000000) (61018022606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (6767295866221303 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-53714261500 / 1000000000000) (-53714260416 / 1000000000000), orderedInterval (11312084698 / 1000000000000) (11312085782 / 1000000000000)))) (orderedInterval (-168585354366 / 1000000000000) (-168585349168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (6322885628755507 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24924523652 / 1000000000000) (-24924523651 / 1000000000000), orderedInterval (-50933935174 / 1000000000000) (-50933935173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (4512309534298531 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27552259412 / 1000000000000) (-27552259411 / 1000000000000), orderedInterval (-61185385441 / 1000000000000) (-61185385440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (5116478085557349 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27635388076 / 1000000000000) (-27635388075 / 1000000000000), orderedInterval (-56640203746 / 1000000000000) (-56640203745 / 1000000000000)))) (orderedInterval (-3699345300 / 1000000000000) (-3699345211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (4265586008082581 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (58317790474 / 1000000000000) (58317821007 / 1000000000000), orderedInterval (-37298094062 / 1000000000000) (-37298063529 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (3768774600386201 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53853907983 / 1000000000000) (-53853815572 / 1000000000000), orderedInterval (50280391191 / 1000000000000) (50280483603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (1092337774237899 / 6400000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (59239841858 / 1000000000000) (59239843225 / 1000000000000), orderedInterval (-15025413908 / 1000000000000) (-15025412541 / 1000000000000)))) (orderedInterval (28604044603 / 1000000000000) (28604060866 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks4_2 :
    compactCertificate202.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (3021463770129553 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67125141572 / 1000000000000) (67125141573 / 1000000000000), orderedInterval (46936788037 / 1000000000000) (46936788038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (2561328299733833 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67356511479 / 1000000000000) (-67356422343 / 1000000000000), orderedInterval (58873278600 / 1000000000000) (58873367737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1602760323687299 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (63998646980 / 1000000000000) (63998646981 / 1000000000000), orderedInterval (92177479169 / 1000000000000) (92177479170 / 1000000000000)))) (orderedInterval (-9619849907 / 1000000000000) (-9619846965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (861969832619133 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81265139027 / 1000000000000) (81265151300 / 1000000000000), orderedInterval (-132013926873 / 1000000000000) (-132013914600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (2340415772576399 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-92881983075 / 1000000000000) (-92881982969 / 1000000000000), orderedInterval (9415740126 / 1000000000000) (9415740232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (3195637649154223 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9309013402 / 1000000000000) (9309013404 / 1000000000000), orderedInterval (79252246152 / 1000000000000) (79252246154 / 1000000000000)))) (orderedInterval (-325350106 / 1000000000000) (-325350091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (1351239676312701 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-101531373654 / 1000000000000) (-101531346643 / 1000000000000), orderedInterval (70248384839 / 1000000000000) (70248411849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (5492714265627421 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202970740 / 1000000000000) (21202971368 / 1000000000000), orderedInterval (-57152292841 / 1000000000000) (-57152292214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (3668878574739539 / 32000000000000) 4 (IntervalRat.scale (1477 / 16) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53566328038 / 1000000000000) (53566407228 / 1000000000000), orderedInterval (-52033704392 / 1000000000000) (-52033625201 / 1000000000000)))) (orderedInterval (-43512450268 / 1000000000000) (-43512413546 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate202_chunkChecks4 :
    compactCertificate202.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate202.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate202_chunkChecks4_0
    compactCertificate202_chunkChecks4_1 compactCertificate202_chunkChecks4_2

theorem compactCertificate202_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate202.chunkCheck r b = true :=
  compactCertificate202.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate202_chunkChecks0
    · exact compactCertificate202_chunkChecks1
    · exact compactCertificate202_chunkChecks2
    · exact compactCertificate202_chunkChecks3
    · exact compactCertificate202_chunkChecks4)

theorem compactCertificate202_coefficient0 :
    compactCertificate202.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate202, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate202_coefficient1 :
    compactCertificate202.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate202, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate202_coefficient2 :
    compactCertificate202.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate202, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate202_coefficient3 :
    compactCertificate202.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate202, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate202_coefficient4 :
    compactCertificate202.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate202, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate202_coefficients : ∀ r : Fin 5,
    compactCertificate202.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate202_coefficient0
  · exact compactCertificate202_coefficient1
  · exact compactCertificate202_coefficient2
  · exact compactCertificate202_coefficient3
  · exact compactCertificate202_coefficient4

theorem compactCertificate202_lower : (1 : ℚ) ≤ compactCertificate202.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate202, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate202_proves {t : ℝ} (ht : t ∈ compactCertificate202.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate202.proves compactCertificate202_states compactCertificate202_chunks
    compactCertificate202_coefficients compactCertificate202_lower ht

end Erdos232
