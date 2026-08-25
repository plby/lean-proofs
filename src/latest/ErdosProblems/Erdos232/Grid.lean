/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.Analytic

open Filter MeasureTheory Metric intervalIntegral
open scoped ENNReal Topology Interval
open LeanCert.Core

namespace Erdos232

def besselGridState000 : IntervalRat × IntervalRat :=
  (orderedInterval (1 / 1) (1 / 1),
   orderedInterval (0 / 1) (0 / 1))

theorem besselGridState000_valid : BesselStateValid 0 besselGridState000 := by
  constructor
  · rw [besselDerivative_zero_eq_initial 0]
    norm_num [besselGridState000, besselInitial, orderedInterval, IntervalRat.mem_def]
  · rw [besselDerivative_zero_eq_initial 1]
    norm_num [besselGridState000, besselInitial, orderedInterval, IntervalRat.mem_def]

def besselGridState001 : IntervalRat × IntervalRat :=
  (orderedInterval (-30378838332141653937262008591875569 / 100000000000000000000000000000000000) (-7594709583035413331840246002997121 / 25000000000000000000000000000000000),
   orderedInterval (-3565550227497488975753968155863171 / 12500000000000000000000000000000000) (-28524401819979911196130720667018283 / 100000000000000000000000000000000000))

theorem besselGridState001_step : besselStateSubset
    (besselIntervalStepZero (157 / 50) 29) besselGridState001 = true := by
  norm_num [besselGridState001, besselStateSubset, rationalIntervalSubset,
    besselIntervalStepZero, besselZeroTransition, besselInitial, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.singleton,
    Finset.sum_range_succ]

theorem besselGridState001_valid : BesselStateValid (1 * 157 / 50 : ℚ) besselGridState001 := by
  have hm : BesselStateValid ((157 / 50 : ℚ) : ℝ) besselGridState001 :=
    BesselStateValid.mono
    (S := besselIntervalStepZero (157 / 50) 29) (T := besselGridState001)
    besselGridState001_step (besselIntervalStepZero_valid (157 / 50) 29)
  convert hm using 1 <;> norm_num

def besselGridState002 : IntervalRat × IntervalRat :=
  (orderedInterval (4391982337527359596012707432259153 / 20000000000000000000000000000000000) (21959911687636799031882194049326047 / 100000000000000000000000000000000000),
   orderedInterval (1332443763467707336629973209043413 / 6250000000000000000000000000000000) (21319100215483318444551744209980839 / 100000000000000000000000000000000000))

theorem besselGridState002_step : besselStateSubset
    (besselIntervalStep (1 * 157 / 50) (157 / 50) 29 besselGridState001) besselGridState002 = true := by
  norm_num [besselGridState001, besselGridState002, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState002_valid : BesselStateValid (2 * 157 / 50 : ℚ) besselGridState002 := by
  have hv := besselIntervalStep_valid (1 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState001 besselGridState001_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (1 * 157 / 50) (157 / 50) 29 besselGridState001)
    (T := besselGridState002) besselGridState002_step hv
  convert hm using 1 <;> norm_num

def besselGridState003 : IntervalRat × IntervalRat :=
  (orderedInterval (-3607295755445686969436929964566973 / 20000000000000000000000000000000000) (-9018239388614216686619113786849701 / 50000000000000000000000000000000000),
   orderedInterval (-1776788562976673594301547983203317 / 10000000000000000000000000000000000) (-3553577125953346890324489815747867 / 20000000000000000000000000000000000))

theorem besselGridState003_step : besselStateSubset
    (besselIntervalStep (2 * 157 / 50) (157 / 50) 29 besselGridState002) besselGridState003 = true := by
  norm_num [besselGridState002, besselGridState003, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState003_valid : BesselStateValid (3 * 157 / 50 : ℚ) besselGridState003 := by
  have hv := besselIntervalStep_valid (2 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState002 besselGridState002_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (2 * 157 / 50) (157 / 50) 29 besselGridState002)
    (T := besselGridState003) besselGridState003_step hv
  convert hm using 1 <;> norm_num

def besselGridState004 : IntervalRat × IntervalRat :=
  (orderedInterval (3912987414006507507642071609909969 / 25000000000000000000000000000000000) (1565194965602603191960861669315171 / 10000000000000000000000000000000000),
   orderedInterval (778048627769472132873100462806733 / 5000000000000000000000000000000000) (972560784711840285819739658130177 / 6250000000000000000000000000000000))

theorem besselGridState004_step : besselStateSubset
    (besselIntervalStep (3 * 157 / 50) (157 / 50) 29 besselGridState003) besselGridState004 = true := by
  norm_num [besselGridState003, besselGridState004, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState004_valid : BesselStateValid (4 * 157 / 50 : ℚ) besselGridState004 := by
  have hv := besselIntervalStep_valid (3 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState003 besselGridState003_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (3 * 157 / 50) (157 / 50) 29 besselGridState003)
    (T := besselGridState004) besselGridState004_step hv
  convert hm using 1 <;> norm_num

def besselGridState005 : IntervalRat × IntervalRat :=
  (orderedInterval (-7003510591452426882170468051165603 / 50000000000000000000000000000000000) (-14007021182904851463913842001288819 / 100000000000000000000000000000000000),
   orderedInterval (-14021574694233856647933029770764369 / 100000000000000000000000000000000000) (-1752696836779231789017841994592773 / 12500000000000000000000000000000000))

theorem besselGridState005_step : besselStateSubset
    (besselIntervalStep (4 * 157 / 50) (157 / 50) 29 besselGridState004) besselGridState005 = true := by
  norm_num [besselGridState004, besselGridState005, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState005_valid : BesselStateValid (5 * 157 / 50 : ℚ) besselGridState005 := by
  have hv := besselIntervalStep_valid (4 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState004 besselGridState004_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (4 * 157 / 50) (157 / 50) 29 besselGridState004)
    (T := besselGridState005) besselGridState005_step hv
  convert hm using 1 <;> norm_num

def besselGridState006 : IntervalRat × IntervalRat :=
  (orderedInterval (199749728378171436343355143992219 / 1562500000000000000000000000000000) (12783982616202974636592540637467903 / 100000000000000000000000000000000000),
   orderedInterval (12870131207197038022990581951618181 / 100000000000000000000000000000000000) (2574026241439408155340179637898159 / 20000000000000000000000000000000000))

theorem besselGridState006_step : besselStateSubset
    (besselIntervalStep (5 * 157 / 50) (157 / 50) 29 besselGridState005) besselGridState006 = true := by
  norm_num [besselGridState005, besselGridState006, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState006_valid : BesselStateValid (6 * 157 / 50 : ℚ) besselGridState006 := by
  have hv := besselIntervalStep_valid (5 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState005 besselGridState005_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (5 * 157 / 50) (157 / 50) 29 besselGridState005)
    (T := besselGridState006) besselGridState006_step hv
  convert hm using 1 <;> norm_num

def besselGridState007 : IntervalRat × IntervalRat :=
  (orderedInterval (-2365657470211638889181135689102673 / 20000000000000000000000000000000000) (-11828287351058191324735038436292703 / 100000000000000000000000000000000000),
   orderedInterval (-11967492925055065695704240124087241 / 100000000000000000000000000000000000) (-1495936615631882815665468579772063 / 12500000000000000000000000000000000))

theorem besselGridState007_step : besselStateSubset
    (besselIntervalStep (6 * 157 / 50) (157 / 50) 29 besselGridState006) besselGridState007 = true := by
  norm_num [besselGridState006, besselGridState007, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState007_valid : BesselStateValid (7 * 157 / 50 : ℚ) besselGridState007 := by
  have hv := besselIntervalStep_valid (6 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState006 besselGridState006_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (6 * 157 / 50) (157 / 50) 29 besselGridState006)
    (T := besselGridState007) besselGridState007_step hv
  convert hm using 1 <;> norm_num

def besselGridState008 : IntervalRat × IntervalRat :=
  (orderedInterval (442182611184355232820572425868437 / 4000000000000000000000000000000000) (11054565279608884352651714331959789 / 100000000000000000000000000000000000),
   orderedInterval (5617804666201001359923537689970109 / 50000000000000000000000000000000000) (1404451166550250788274745655329063 / 12500000000000000000000000000000000))

theorem besselGridState008_step : besselStateSubset
    (besselIntervalStep (7 * 157 / 50) (157 / 50) 29 besselGridState007) besselGridState008 = true := by
  norm_num [besselGridState007, besselGridState008, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState008_valid : BesselStateValid (8 * 157 / 50 : ℚ) besselGridState008 := by
  have hv := besselIntervalStep_valid (7 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState007 besselGridState007_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (7 * 157 / 50) (157 / 50) 29 besselGridState007)
    (T := besselGridState008) besselGridState008_step hv
  convert hm using 1 <;> norm_num

def besselGridState009 : IntervalRat × IntervalRat :=
  (orderedInterval (-10411313264261052148326844384042213 / 100000000000000000000000000000000000) (-5205656632130524102388729436992987 / 50000000000000000000000000000000000),
   orderedInterval (-1328359611628132054045129163132731 / 12500000000000000000000000000000000) (-332089902907032888450079585578831 / 3125000000000000000000000000000000))

theorem besselGridState009_step : besselStateSubset
    (besselIntervalStep (8 * 157 / 50) (157 / 50) 29 besselGridState008) besselGridState009 = true := by
  norm_num [besselGridState008, besselGridState009, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState009_valid : BesselStateValid (9 * 157 / 50 : ℚ) besselGridState009 := by
  have hv := besselIntervalStep_valid (8 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState008 besselGridState008_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (8 * 157 / 50) (157 / 50) 29 besselGridState008)
    (T := besselGridState009) besselGridState009_step hv
  convert hm using 1 <;> norm_num

def besselGridState010 : IntervalRat × IntervalRat :=
  (orderedInterval (4932687204578661842516616997073179 / 50000000000000000000000000000000000) (4932687204578664020230077863608653 / 50000000000000000000000000000000000),
   orderedInterval (2022079859018831838106758490010291 / 20000000000000000000000000000000000) (2527599823773540901989221685533969 / 25000000000000000000000000000000000))

theorem besselGridState010_step : besselStateSubset
    (besselIntervalStep (9 * 157 / 50) (157 / 50) 29 besselGridState009) besselGridState010 = true := by
  norm_num [besselGridState009, besselGridState010, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState010_valid : BesselStateValid (10 * 157 / 50 : ℚ) besselGridState010 := by
  have hv := besselIntervalStep_valid (9 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState009 besselGridState009_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (9 * 157 / 50) (157 / 50) 29 besselGridState009)
    (T := besselGridState010) besselGridState010_step hv
  convert hm using 1 <;> norm_num

def besselGridState011 : IntervalRat × IntervalRat :=
  (orderedInterval (-9394309144088048074689008924998461 / 100000000000000000000000000000000000) (-9394309144088043306905000763355297 / 100000000000000000000000000000000000),
   orderedInterval (-4832567925029249909510599472644973 / 50000000000000000000000000000000000) (-386605434002339799445039127069793 / 4000000000000000000000000000000000))

theorem besselGridState011_step : besselStateSubset
    (besselIntervalStep (10 * 157 / 50) (157 / 50) 29 besselGridState010) besselGridState011 = true := by
  norm_num [besselGridState010, besselGridState011, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState011_valid : BesselStateValid (11 * 157 / 50 : ℚ) besselGridState011 := by
  have hv := besselIntervalStep_valid (10 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState010 besselGridState010_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (10 * 157 / 50) (157 / 50) 29 besselGridState010)
    (T := besselGridState011) besselGridState011_step hv
  convert hm using 1 <;> norm_num

def besselGridState012 : IntervalRat × IntervalRat :=
  (orderedInterval (8982316384700499117736147805440699 / 100000000000000000000000000000000000) (8982316384700504298366876501611267 / 100000000000000000000000000000000000),
   orderedInterval (9276197452543848391442693548717221 / 100000000000000000000000000000000000) (1855239490508770727984935256643091 / 20000000000000000000000000000000000))

theorem besselGridState012_step : besselStateSubset
    (besselIntervalStep (11 * 157 / 50) (157 / 50) 29 besselGridState011) besselGridState012 = true := by
  norm_num [besselGridState011, besselGridState012, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState012_valid : BesselStateValid (12 * 157 / 50 : ℚ) besselGridState012 := by
  have hv := besselIntervalStep_valid (11 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState011 besselGridState011_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (11 * 157 / 50) (157 / 50) 29 besselGridState011)
    (T := besselGridState012) besselGridState012_step hv
  convert hm using 1 <;> norm_num

def besselGridState013 : IntervalRat × IntervalRat :=
  (orderedInterval (-4308952208135487042565197355154539 / 50000000000000000000000000000000000) (-8617904416270968491155763870052207 / 100000000000000000000000000000000000),
   orderedInterval (-4466356425223371262027219040112689 / 50000000000000000000000000000000000) (-8932712850446736859792371125575551 / 100000000000000000000000000000000000))

theorem besselGridState013_step : besselStateSubset
    (besselIntervalStep (12 * 157 / 50) (157 / 50) 29 besselGridState012) besselGridState013 = true := by
  norm_num [besselGridState012, besselGridState013, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState013_valid : BesselStateValid (13 * 157 / 50 : ℚ) besselGridState013 := by
  have hv := besselIntervalStep_valid (12 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState012 besselGridState012_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (12 * 157 / 50) (157 / 50) 29 besselGridState012)
    (T := besselGridState013) besselGridState013_step hv
  convert hm using 1 <;> norm_num

def besselGridState014 : IntervalRat × IntervalRat :=
  (orderedInterval (4146244250388216331004594636613773 / 50000000000000000000000000000000000) (4146244250388219334915369789817391 / 50000000000000000000000000000000000),
   orderedInterval (1725306945723731248321016837089031 / 20000000000000000000000000000000000) (1725306945723732464379981943454451 / 20000000000000000000000000000000000))

theorem besselGridState014_step : besselStateSubset
    (besselIntervalStep (13 * 157 / 50) (157 / 50) 29 besselGridState013) besselGridState014 = true := by
  norm_num [besselGridState013, besselGridState014, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState014_valid : BesselStateValid (14 * 157 / 50 : ℚ) besselGridState014 := by
  have hv := besselIntervalStep_valid (13 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState013 besselGridState013_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (13 * 157 / 50) (157 / 50) 29 besselGridState013)
    (T := besselGridState014) besselGridState014_step hv
  convert hm using 1 <;> norm_num

def besselGridState015 : IntervalRat × IntervalRat :=
  (orderedInterval (-799950877487447146172584717448027 / 10000000000000000000000000000000000) (-99993859685930812994371480793903 / 1250000000000000000000000000000000),
   orderedInterval (-8351421045379389908314463037289361 / 100000000000000000000000000000000000) (-8351421045379383411688417354326619 / 100000000000000000000000000000000000))

theorem besselGridState015_step : besselStateSubset
    (besselIntervalStep (14 * 157 / 50) (157 / 50) 29 besselGridState014) besselGridState015 = true := by
  norm_num [besselGridState014, besselGridState015, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState015_valid : BesselStateValid (15 * 157 / 50 : ℚ) besselGridState015 := by
  have hv := besselIntervalStep_valid (14 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState014 besselGridState014_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (14 * 157 / 50) (157 / 50) 29 besselGridState014)
    (T := besselGridState015) besselGridState015_step hv
  convert hm using 1 <;> norm_num

def besselGridState016 : IntervalRat × IntervalRat :=
  (orderedInterval (154677093977849749112768327976607 / 2000000000000000000000000000000000) (966731837361561786585070959080827 / 12500000000000000000000000000000000),
   orderedInterval (8102498238431302889112912840095841 / 100000000000000000000000000000000000) (8102498238431309802404655854958331 / 100000000000000000000000000000000000))

theorem besselGridState016_step : besselStateSubset
    (besselIntervalStep (15 * 157 / 50) (157 / 50) 29 besselGridState015) besselGridState016 = true := by
  norm_num [besselGridState015, besselGridState016, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState016_valid : BesselStateValid (16 * 157 / 50 : ℚ) besselGridState016 := by
  have hv := besselIntervalStep_valid (15 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState015 besselGridState015_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (15 * 157 / 50) (157 / 50) 29 besselGridState015)
    (T := besselGridState016) besselGridState016_step hv
  convert hm using 1 <;> norm_num

def besselGridState017 : IntervalRat × IntervalRat :=
  (orderedInterval (-7491477619109904711247973584088023 / 100000000000000000000000000000000000) (-3745738809554948729412599623791747 / 50000000000000000000000000000000000),
   orderedInterval (-1968974591221965602691106598727597 / 25000000000000000000000000000000000) (-3937949182443927540221846981127889 / 50000000000000000000000000000000000))

theorem besselGridState017_step : besselStateSubset
    (besselIntervalStep (16 * 157 / 50) (157 / 50) 29 besselGridState016) besselGridState017 = true := by
  norm_num [besselGridState016, besselGridState017, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState017_valid : BesselStateValid (17 * 157 / 50 : ℚ) besselGridState017 := by
  have hv := besselIntervalStep_valid (16 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState016 besselGridState016_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (16 * 157 / 50) (157 / 50) 29 besselGridState016)
    (T := besselGridState017) besselGridState017_step hv
  convert hm using 1 <;> norm_num

def besselGridState018 : IntervalRat × IntervalRat :=
  (orderedInterval (7269122847426909788623977140639199 / 100000000000000000000000000000000000) (7269122847426917456944660083510831 / 100000000000000000000000000000000000),
   orderedInterval (479281704838134106623449761248921 / 6250000000000000000000000000000000) (7668507277410153453711613111933399 / 100000000000000000000000000000000000))

theorem besselGridState018_step : besselStateSubset
    (besselIntervalStep (17 * 157 / 50) (157 / 50) 29 besselGridState017) besselGridState018 = true := by
  norm_num [besselGridState017, besselGridState018, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState018_valid : BesselStateValid (18 * 157 / 50 : ℚ) besselGridState018 := by
  have hv := besselIntervalStep_valid (17 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState017 besselGridState017_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (17 * 157 / 50) (157 / 50) 29 besselGridState017)
    (T := besselGridState018) besselGridState018_step hv
  convert hm using 1 <;> norm_num

def besselGridState019 : IntervalRat × IntervalRat :=
  (orderedInterval (-1412827998810374121700275988319799 / 20000000000000000000000000000000000) (-1766034998512965630940794329696391 / 25000000000000000000000000000000000),
   orderedInterval (-373889289985501044323197999724231 / 5000000000000000000000000000000000) (-934723224963751590113237371471607 / 12500000000000000000000000000000000))

theorem besselGridState019_step : besselStateSubset
    (besselIntervalStep (18 * 157 / 50) (157 / 50) 29 besselGridState018) besselGridState019 = true := by
  norm_num [besselGridState018, besselGridState019, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState019_valid : BesselStateValid (19 * 157 / 50 : ℚ) besselGridState019 := by
  have hv := besselIntervalStep_valid (18 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState018 besselGridState018_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (18 * 157 / 50) (157 / 50) 29 besselGridState018)
    (T := besselGridState019) besselGridState019_step hv
  convert hm using 1 <;> norm_num

def besselGridState020 : IntervalRat × IntervalRat :=
  (orderedInterval (1718586475000914234274209493186563 / 25000000000000000000000000000000000) (6874345900003665438774218338004121 / 100000000000000000000000000000000000),
   orderedInterval (456352509147825396179525127543711 / 6250000000000000000000000000000000) (7301640146365214922674117748344159 / 100000000000000000000000000000000000))

theorem besselGridState020_step : besselStateSubset
    (besselIntervalStep (19 * 157 / 50) (157 / 50) 29 besselGridState019) besselGridState020 = true := by
  norm_num [besselGridState019, besselGridState020, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState020_valid : BesselStateValid (20 * 157 / 50 : ℚ) besselGridState020 := by
  have hv := besselIntervalStep_valid (19 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState019 besselGridState019_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (19 * 157 / 50) (157 / 50) 29 besselGridState019)
    (T := besselGridState020) besselGridState020_step hv
  convert hm using 1 <;> norm_num

def besselGridState021 : IntervalRat × IntervalRat :=
  (orderedInterval (-6697923754825056282777579658420949 / 100000000000000000000000000000000000) (-669792375482504736363753529316467 / 10000000000000000000000000000000000),
   orderedInterval (-71383263259494887796996668910189 / 1000000000000000000000000000000000) (-7138326325949479777218764424030359 / 100000000000000000000000000000000000))

theorem besselGridState021_step : besselStateSubset
    (besselIntervalStep (20 * 157 / 50) (157 / 50) 29 besselGridState020) besselGridState021 = true := by
  norm_num [besselGridState020, besselGridState021, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState021_valid : BesselStateValid (21 * 157 / 50 : ℚ) besselGridState021 := by
  have hv := besselIntervalStep_valid (20 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState020 besselGridState020_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (20 * 157 / 50) (157 / 50) 29 besselGridState020)
    (T := besselGridState021) besselGridState021_step hv
  convert hm using 1 <;> norm_num

def besselGridState022 : IntervalRat × IntervalRat :=
  (orderedInterval (1306669525047363731573472280215273 / 20000000000000000000000000000000000) (1633336906309206998748802559912553 / 25000000000000000000000000000000000),
   orderedInterval (698637847501658209608672186949279 / 10000000000000000000000000000000000) (1746594618754147879423462259949489 / 25000000000000000000000000000000000))

theorem besselGridState022_step : besselStateSubset
    (besselIntervalStep (21 * 157 / 50) (157 / 50) 29 besselGridState021) besselGridState022 = true := by
  norm_num [besselGridState021, besselGridState022, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState022_valid : BesselStateValid (22 * 157 / 50 : ℚ) besselGridState022 := by
  have hv := besselIntervalStep_valid (21 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState021 besselGridState021_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (21 * 157 / 50) (157 / 50) 29 besselGridState021)
    (T := besselGridState022) besselGridState022_step hv
  convert hm using 1 <;> norm_num

def besselGridState023 : IntervalRat × IntervalRat :=
  (orderedInterval (-3189662580166097491303670926129417 / 50000000000000000000000000000000000) (-637932516033218522696503371908149 / 10000000000000000000000000000000000),
   orderedInterval (-6844554352041377047573526483943687 / 100000000000000000000000000000000000) (-6844554352041367206383254705057421 / 100000000000000000000000000000000000))

theorem besselGridState023_step : besselStateSubset
    (besselIntervalStep (22 * 157 / 50) (157 / 50) 29 besselGridState022) besselGridState023 = true := by
  norm_num [besselGridState022, besselGridState023, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState023_valid : BesselStateValid (23 * 157 / 50 : ℚ) besselGridState023 := by
  have hv := besselIntervalStep_valid (22 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState022 besselGridState022_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (22 * 157 / 50) (157 / 50) 29 besselGridState022)
    (T := besselGridState023) besselGridState023_step hv
  convert hm using 1 <;> norm_num

def besselGridState024 : IntervalRat × IntervalRat :=
  (orderedInterval (1246950703182269449428642261671897 / 20000000000000000000000000000000000) (6234753515911357421828034347910947 / 100000000000000000000000000000000000),
   orderedInterval (6711793338564779461352453864381101 / 100000000000000000000000000000000000) (6711793338564789722591350657567787 / 100000000000000000000000000000000000))

theorem besselGridState024_step : besselStateSubset
    (besselIntervalStep (23 * 157 / 50) (157 / 50) 29 besselGridState023) besselGridState024 = true := by
  norm_num [besselGridState023, besselGridState024, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState024_valid : BesselStateValid (24 * 157 / 50 : ℚ) besselGridState024 := by
  have hv := besselIntervalStep_valid (23 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState023 besselGridState023_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (23 * 157 / 50) (157 / 50) 29 besselGridState023)
    (T := besselGridState024) besselGridState024_step hv
  convert hm using 1 <;> norm_num

def besselGridState025 : IntervalRat × IntervalRat :=
  (orderedInterval (-121973700759483025251702958799371 / 2000000000000000000000000000000000) (-6098685037974140668328446611538223 / 100000000000000000000000000000000000),
   orderedInterval (-3293591846024703819429023238760351 / 50000000000000000000000000000000000) (-6587183692049396957097568930387819 / 100000000000000000000000000000000000))

theorem besselGridState025_step : besselStateSubset
    (besselIntervalStep (24 * 157 / 50) (157 / 50) 29 besselGridState024) besselGridState025 = true := by
  norm_num [besselGridState024, besselGridState025, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState025_valid : BesselStateValid (25 * 157 / 50 : ℚ) besselGridState025 := by
  have hv := besselIntervalStep_valid (24 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState024 besselGridState024_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (24 * 157 / 50) (157 / 50) 29 besselGridState024)
    (T := besselGridState025) besselGridState025_step hv
  convert hm using 1 <;> norm_num

def besselGridState026 : IntervalRat × IntervalRat :=
  (orderedInterval (2985150124999857601033186711876047 / 50000000000000000000000000000000000) (1194060049999945243285109476373097 / 20000000000000000000000000000000000),
   orderedInterval (3234968367488867382239753933063509 / 50000000000000000000000000000000000) (646993673497774586724109867715071 / 10000000000000000000000000000000000))

theorem besselGridState026_step : besselStateSubset
    (besselIntervalStep (25 * 157 / 50) (157 / 50) 29 besselGridState025) besselGridState026 = true := by
  norm_num [besselGridState025, besselGridState026, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState026_valid : BesselStateValid (26 * 157 / 50 : ℚ) besselGridState026 := by
  have hv := besselIntervalStep_valid (25 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState025 besselGridState025_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (25 * 157 / 50) (157 / 50) 29 besselGridState025)
    (T := besselGridState026) besselGridState026_step hv
  convert hm using 1 <;> norm_num

def besselGridState027 : IntervalRat × IntervalRat :=
  (orderedInterval (-116977727499314717100765115108003 / 2000000000000000000000000000000000) (-2924443187482862210022423881478803 / 50000000000000000000000000000000000),
   orderedInterval (-6359366308541960154382877563235843 / 100000000000000000000000000000000000) (-635936630854194863013481395416003 / 10000000000000000000000000000000000))

theorem besselGridState027_step : besselStateSubset
    (besselIntervalStep (26 * 157 / 50) (157 / 50) 29 besselGridState026) besselGridState027 = true := by
  norm_num [besselGridState026, besselGridState027, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState027_valid : BesselStateValid (27 * 157 / 50 : ℚ) besselGridState027 := by
  have hv := besselIntervalStep_valid (26 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState026 besselGridState026_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (26 * 157 / 50) (157 / 50) 29 besselGridState026)
    (T := besselGridState027) besselGridState027_step hv
  convert hm using 1 <;> norm_num

def besselGridState028 : IntervalRat × IntervalRat :=
  (orderedInterval (358363756234873619525610027002649 / 6250000000000000000000000000000000) (5733820099757989768570277423580519 / 100000000000000000000000000000000000),
   orderedInterval (1563718066867214695233541858460891 / 25000000000000000000000000000000000) (6254872267468870727159260414666393 / 100000000000000000000000000000000000))

theorem besselGridState028_step : besselStateSubset
    (besselIntervalStep (27 * 157 / 50) (157 / 50) 29 besselGridState027) besselGridState028 = true := by
  norm_num [besselGridState027, besselGridState028, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState028_valid : BesselStateValid (28 * 157 / 50 : ℚ) besselGridState028 := by
  have hv := besselIntervalStep_valid (27 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState027 besselGridState027_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (27 * 157 / 50) (157 / 50) 29 besselGridState027)
    (T := besselGridState028) besselGridState028_step hv
  convert hm using 1 <;> norm_num

def besselGridState029 : IntervalRat × IntervalRat :=
  (orderedInterval (-5624553625775746950204624613756383 / 100000000000000000000000000000000000) (-703069203221966834042881896675833 / 12500000000000000000000000000000000),
   orderedInterval (-384745444327236621223094831727129 / 6250000000000000000000000000000000) (-6155927109235773570872174140675821 / 100000000000000000000000000000000000))

theorem besselGridState029_step : besselStateSubset
    (besselIntervalStep (28 * 157 / 50) (157 / 50) 29 besselGridState028) besselGridState029 = true := by
  norm_num [besselGridState028, besselGridState029, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState029_valid : BesselStateValid (29 * 157 / 50 : ℚ) besselGridState029 := by
  have hv := besselIntervalStep_valid (28 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState028 besselGridState028_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (28 * 157 / 50) (157 / 50) 29 besselGridState028)
    (T := besselGridState029) besselGridState029_step hv
  convert hm using 1 <;> norm_num

def besselGridState030 : IntervalRat × IntervalRat :=
  (orderedInterval (1104120657981892563076193399260793 / 20000000000000000000000000000000000) (2760301644954737757739281317620197 / 50000000000000000000000000000000000),
   orderedInterval (6062065057831476457371247376594017 / 100000000000000000000000000000000000) (3031032528915744624520136231612347 / 50000000000000000000000000000000000))

theorem besselGridState030_step : besselStateSubset
    (besselIntervalStep (29 * 157 / 50) (157 / 50) 29 besselGridState029) besselGridState030 = true := by
  norm_num [besselGridState029, besselGridState030, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState030_valid : BesselStateValid (30 * 157 / 50 : ℚ) besselGridState030 := by
  have hv := besselIntervalStep_valid (29 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState029 besselGridState029_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (29 * 157 / 50) (157 / 50) 29 besselGridState029)
    (T := besselGridState030) besselGridState030_step hv
  convert hm using 1 <;> norm_num

def besselGridState031 : IntervalRat × IntervalRat :=
  (orderedInterval (-2710770107086145239335084575098401 / 50000000000000000000000000000000000) (-2710770107086138677900287887110823 / 50000000000000000000000000000000000),
   orderedInterval (-5972873086848468327067858695454519 / 100000000000000000000000000000000000) (-5972873086848455111923896894889051 / 100000000000000000000000000000000000))

theorem besselGridState031_step : besselStateSubset
    (besselIntervalStep (30 * 157 / 50) (157 / 50) 29 besselGridState030) besselGridState031 = true := by
  norm_num [besselGridState030, besselGridState031, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState031_valid : BesselStateValid (31 * 157 / 50 : ℚ) besselGridState031 := by
  have hv := besselIntervalStep_valid (30 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState030 besselGridState030_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (30 * 157 / 50) (157 / 50) 29 besselGridState030)
    (T := besselGridState031) besselGridState031_step hv
  convert hm using 1 <;> norm_num

def besselGridState032 : IntervalRat × IntervalRat :=
  (orderedInterval (133174564247038887409220250057941 / 2500000000000000000000000000000000) (5326982569881569042547342634101051 / 100000000000000000000000000000000000),
   orderedInterval (5887983487557195299716510292334279 / 100000000000000000000000000000000000) (1177596697511441787768430616898741 / 20000000000000000000000000000000000))

theorem besselGridState032_step : besselStateSubset
    (besselIntervalStep (31 * 157 / 50) (157 / 50) 29 besselGridState031) besselGridState032 = true := by
  norm_num [besselGridState031, besselGridState032, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState032_valid : BesselStateValid (32 * 157 / 50 : ℚ) besselGridState032 := by
  have hv := besselIntervalStep_valid (31 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState031 besselGridState031_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (31 * 157 / 50) (157 / 50) 29 besselGridState031)
    (T := besselGridState032) besselGridState032_step hv
  convert hm using 1 <;> norm_num

def besselGridState033 : IntervalRat × IntervalRat :=
  (orderedInterval (-5236589136865635764437399681977827 / 100000000000000000000000000000000000) (-130914728421640544860301004517057 / 2500000000000000000000000000000000),
   orderedInterval (-2903533838660256110621021478292381 / 50000000000000000000000000000000000) (-232282707092819926304990947952479 / 4000000000000000000000000000000000))

theorem besselGridState033_step : besselStateSubset
    (besselIntervalStep (32 * 157 / 50) (157 / 50) 29 besselGridState032) besselGridState033 = true := by
  norm_num [besselGridState032, besselGridState033, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState033_valid : BesselStateValid (33 * 157 / 50 : ℚ) besselGridState033 := by
  have hv := besselIntervalStep_valid (32 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState032 besselGridState032_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (32 * 157 / 50) (157 / 50) 29 besselGridState032)
    (T := besselGridState033) besselGridState033_step hv
  convert hm using 1 <;> norm_num

def besselGridState034 : IntervalRat × IntervalRat :=
  (orderedInterval (2575026954494373543711502423314661 / 50000000000000000000000000000000000) (206002156359550459273360173286433 / 4000000000000000000000000000000000),
   orderedInterval (5729831010967753850861442166383559 / 100000000000000000000000000000000000) (5729831010967768339483234282556679 / 100000000000000000000000000000000000))

theorem besselGridState034_step : besselStateSubset
    (besselIntervalStep (33 * 157 / 50) (157 / 50) 29 besselGridState033) besselGridState034 = true := by
  norm_num [besselGridState033, besselGridState034, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState034_valid : BesselStateValid (34 * 157 / 50 : ℚ) besselGridState034 := by
  have hv := besselIntervalStep_valid (33 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState033 besselGridState033_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (33 * 157 / 50) (157 / 50) 29 besselGridState033)
    (T := besselGridState034) besselGridState034_step hv
  convert hm using 1 <;> norm_num

def besselGridState035 : IntervalRat × IntervalRat :=
  (orderedInterval (-1266775387706555912257901987099693 / 25000000000000000000000000000000000) (-2533550775413104414847623840019693 / 50000000000000000000000000000000000),
   orderedInterval (-1131201681732554217751717076937059 / 20000000000000000000000000000000000) (-2828004204331378087308320651208703 / 50000000000000000000000000000000000))

theorem besselGridState035_step : besselStateSubset
    (besselIntervalStep (34 * 157 / 50) (157 / 50) 29 besselGridState034) besselGridState035 = true := by
  norm_num [besselGridState034, besselGridState035, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState035_valid : BesselStateValid (35 * 157 / 50 : ℚ) besselGridState035 := by
  have hv := besselIntervalStep_valid (34 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState034 besselGridState034_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (34 * 157 / 50) (157 / 50) 29 besselGridState034)
    (T := besselGridState035) besselGridState035_step hv
  convert hm using 1 <;> norm_num

def besselGridState036 : IntervalRat × IntervalRat :=
  (orderedInterval (997496710232201964746663004932433 / 20000000000000000000000000000000000) (4987483551161025068535649095758169 / 100000000000000000000000000000000000),
   orderedInterval (2792680326340657201715088794953409 / 50000000000000000000000000000000000) (2792680326340664871805222230584021 / 50000000000000000000000000000000000))

theorem besselGridState036_step : besselStateSubset
    (besselIntervalStep (35 * 157 / 50) (157 / 50) 29 besselGridState035) besselGridState036 = true := by
  norm_num [besselGridState035, besselGridState036, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState036_valid : BesselStateValid (36 * 157 / 50 : ℚ) besselGridState036 := by
  have hv := besselIntervalStep_valid (35 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState035 besselGridState035_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (35 * 157 / 50) (157 / 50) 29 besselGridState035)
    (T := besselGridState036) besselGridState036_step hv
  convert hm using 1 <;> norm_num

def besselGridState037 : IntervalRat × IntervalRat :=
  (orderedInterval (-4910974950390227676269120442187021 / 100000000000000000000000000000000000) (-4910974950390212005459320783393593 / 100000000000000000000000000000000000),
   orderedInterval (-172427226108060290772334033031993 / 3125000000000000000000000000000000) (-2758835617728956768987777336400649 / 50000000000000000000000000000000000))

theorem besselGridState037_step : besselStateSubset
    (besselIntervalStep (36 * 157 / 50) (157 / 50) 29 besselGridState036) besselGridState037 = true := by
  norm_num [besselGridState036, besselGridState037, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState037_valid : BesselStateValid (37 * 157 / 50 : ℚ) besselGridState037 := by
  have hv := besselIntervalStep_valid (36 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState036 besselGridState036_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (36 * 157 / 50) (157 / 50) 29 besselGridState036)
    (T := besselGridState037) besselGridState037_step hv
  convert hm using 1 <;> norm_num

def besselGridState038 : IntervalRat × IntervalRat :=
  (orderedInterval (4837371543287874625994434296854213 / 100000000000000000000000000000000000) (1209342885821972680838514588597503 / 25000000000000000000000000000000000),
   orderedInterval (1363185916125134135845517681574281 / 25000000000000000000000000000000000) (1090548732900110547440568657028959 / 20000000000000000000000000000000000))

theorem besselGridState038_step : besselStateSubset
    (besselIntervalStep (37 * 157 / 50) (157 / 50) 29 besselGridState037) besselGridState038 = true := by
  norm_num [besselGridState037, besselGridState038, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState038_valid : BesselStateValid (38 * 157 / 50 : ℚ) besselGridState038 := by
  have hv := besselIntervalStep_valid (37 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState037 besselGridState037_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (37 * 157 / 50) (157 / 50) 29 besselGridState037)
    (T := besselGridState038) besselGridState038_step hv
  convert hm using 1 <;> norm_num

def besselGridState039 : IntervalRat × IntervalRat :=
  (orderedInterval (-4766487477599680298754779469227067 / 100000000000000000000000000000000000) (-238324373879983188715105771926151 / 5000000000000000000000000000000000),
   orderedInterval (-26951995739717506314438485184137 / 500000000000000000000000000000000) (-2695199573971742320730210299268479 / 50000000000000000000000000000000000))

theorem besselGridState039_step : besselStateSubset
    (besselIntervalStep (38 * 157 / 50) (157 / 50) 29 besselGridState038) besselGridState039 = true := by
  norm_num [besselGridState038, besselGridState039, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState039_valid : BesselStateValid (39 * 157 / 50 : ℚ) besselGridState039 := by
  have hv := besselIntervalStep_valid (38 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState038 besselGridState038_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (38 * 157 / 50) (157 / 50) 29 besselGridState038)
    (T := besselGridState039) besselGridState039_step hv
  convert hm using 1 <;> norm_num

def besselGridState040 : IntervalRat × IntervalRat :=
  (orderedInterval (1174538295978156258230600015249471 / 25000000000000000000000000000000000) (939630636782528397002433482841223 / 20000000000000000000000000000000000),
   orderedInterval (533047459881439805681530250429607 / 10000000000000000000000000000000000) (1332618649703603776593981853009933 / 25000000000000000000000000000000000))

theorem besselGridState040_step : besselStateSubset
    (besselIntervalStep (39 * 157 / 50) (157 / 50) 29 besselGridState039) besselGridState040 = true := by
  norm_num [besselGridState039, besselGridState040, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState040_valid : BesselStateValid (40 * 157 / 50 : ℚ) besselGridState040 := by
  have hv := besselIntervalStep_valid (39 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState039 besselGridState039_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (39 * 157 / 50) (157 / 50) 29 besselGridState039)
    (T := besselGridState040) besselGridState040_step hv
  convert hm using 1 <;> norm_num

def besselGridState041 : IntervalRat × IntervalRat :=
  (orderedInterval (-2316106792048400836764302596370273 / 50000000000000000000000000000000000) (-2316106792048392146628415638579871 / 50000000000000000000000000000000000),
   orderedInterval (-4218256725943796431168609828801 / 80000000000000000000000000000000) (-5272820907429728060738068819433527 / 100000000000000000000000000000000000))

theorem besselGridState041_step : besselStateSubset
    (besselIntervalStep (40 * 157 / 50) (157 / 50) 29 besselGridState040) besselGridState041 = true := by
  norm_num [besselGridState040, besselGridState041, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState041_valid : BesselStateValid (41 * 157 / 50 : ℚ) besselGridState041 := by
  have hv := besselIntervalStep_valid (40 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState040 besselGridState040_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (40 * 157 / 50) (157 / 50) 29 besselGridState040)
    (T := besselGridState041) besselGridState041_step hv
  convert hm using 1 <;> norm_num

def besselGridState042 : IntervalRat × IntervalRat :=
  (orderedInterval (4568526535060531295100341185853237 / 100000000000000000000000000000000000) (2284263267530274552049928935002329 / 50000000000000000000000000000000000),
   orderedInterval (5217301440374523958924398726157283 / 100000000000000000000000000000000000) (5217301440374541866339664064540277 / 100000000000000000000000000000000000))

theorem besselGridState042_step : besselStateSubset
    (besselIntervalStep (41 * 157 / 50) (157 / 50) 29 besselGridState041) besselGridState042 = true := by
  norm_num [besselGridState041, besselGridState042, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState042_valid : BesselStateValid (42 * 157 / 50 : ℚ) besselGridState042 := by
  have hv := besselIntervalStep_valid (41 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState041 besselGridState041_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (41 * 157 / 50) (157 / 50) 29 besselGridState041)
    (T := besselGridState042) besselGridState042_step hv
  convert hm using 1 <;> norm_num

def besselGridState043 : IntervalRat × IntervalRat :=
  (orderedInterval (-1126740368033284855001359429262161 / 25000000000000000000000000000000000) (-4506961472133121181731615178079833 / 100000000000000000000000000000000000),
   orderedInterval (-1032758146355061135967309730505833 / 20000000000000000000000000000000000) (-5163790731775287342696507483491393 / 100000000000000000000000000000000000))

theorem besselGridState043_step : besselStateSubset
    (besselIntervalStep (42 * 157 / 50) (157 / 50) 29 besselGridState042) besselGridState043 = true := by
  norm_num [besselGridState042, besselGridState043, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState043_valid : BesselStateValid (43 * 157 / 50 : ℚ) besselGridState043 := by
  have hv := besselIntervalStep_valid (42 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState042 besselGridState042_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (42 * 157 / 50) (157 / 50) 29 besselGridState042)
    (T := besselGridState043) besselGridState043_step hv
  convert hm using 1 <;> norm_num

def besselGridState044 : IntervalRat × IntervalRat :=
  (orderedInterval (1111849555622793512923452350140449 / 25000000000000000000000000000000000) (4447398222491192719789322408018937 / 100000000000000000000000000000000000),
   orderedInterval (319510833651580337743447790949639 / 6250000000000000000000000000000000) (2556086669212652085646906087576951 / 50000000000000000000000000000000000))

theorem besselGridState044_step : besselStateSubset
    (besselIntervalStep (43 * 157 / 50) (157 / 50) 29 besselGridState043) besselGridState044 = true := by
  norm_num [besselGridState043, besselGridState044, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState044_valid : BesselStateValid (44 * 157 / 50 : ℚ) besselGridState044 := by
  have hv := besselIntervalStep_valid (43 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState043 besselGridState043_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (43 * 157 / 50) (157 / 50) 29 besselGridState043)
    (T := besselGridState044) besselGridState044_step hv
  convert hm using 1 <;> norm_num

def besselGridState045 : IntervalRat × IntervalRat :=
  (orderedInterval (-2194862981996379009813394973975359 / 50000000000000000000000000000000000) (-4389725963992738921161385039142223 / 100000000000000000000000000000000000),
   orderedInterval (-506234283506636417326904864230479 / 10000000000000000000000000000000000) (-5062342835066344975076404312332303 / 100000000000000000000000000000000000))

theorem besselGridState045_step : besselStateSubset
    (besselIntervalStep (44 * 157 / 50) (157 / 50) 29 besselGridState044) besselGridState045 = true := by
  norm_num [besselGridState044, besselGridState045, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState045_valid : BesselStateValid (45 * 157 / 50 : ℚ) besselGridState045 := by
  have hv := besselIntervalStep_valid (44 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState044 besselGridState044_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (44 * 157 / 50) (157 / 50) 29 besselGridState044)
    (T := besselGridState045) besselGridState045_step hv
  convert hm using 1 <;> norm_num

def besselGridState046 : IntervalRat × IntervalRat :=
  (orderedInterval (2166921154406029491215487065065343 / 50000000000000000000000000000000000) (4333842308812078511815285051807723 / 100000000000000000000000000000000000),
   orderedInterval (5014200929998345643823069653524789 / 100000000000000000000000000000000000) (200568037199934610933864045763799 / 4000000000000000000000000000000000))

theorem besselGridState046_step : besselStateSubset
    (besselIntervalStep (45 * 157 / 50) (157 / 50) 29 besselGridState045) besselGridState046 = true := by
  norm_num [besselGridState045, besselGridState046, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState046_valid : BesselStateValid (46 * 157 / 50 : ℚ) besselGridState046 := by
  have hv := besselIntervalStep_valid (45 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState045 besselGridState045_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (45 * 157 / 50) (157 / 50) 29 besselGridState045)
    (T := besselGridState046) besselGridState046_step hv
  convert hm using 1 <;> norm_num

def besselGridState047 : IntervalRat × IntervalRat :=
  (orderedInterval (-213982624728332378808342027635653 / 5000000000000000000000000000000000) (-171186099782665104612552018678789 / 4000000000000000000000000000000000),
   orderedInterval (-4967656684354892813820046721926983 / 100000000000000000000000000000000000) (-2483828342177436376213646032658757 / 50000000000000000000000000000000000))

theorem besselGridState047_step : besselStateSubset
    (besselIntervalStep (46 * 157 / 50) (157 / 50) 29 besselGridState046) besselGridState047 = true := by
  norm_num [besselGridState046, besselGridState047, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState047_valid : BesselStateValid (47 * 157 / 50 : ℚ) besselGridState047 := by
  have hv := besselIntervalStep_valid (46 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState046 besselGridState046_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (46 * 157 / 50) (157 / 50) 29 besselGridState046)
    (T := besselGridState047) besselGridState047_step hv
  convert hm using 1 <;> norm_num

def besselGridState048 : IntervalRat × IntervalRat :=
  (orderedInterval (4227068668340633479250751359130221 / 100000000000000000000000000000000000) (2113534334170326936061574802601389 / 50000000000000000000000000000000000),
   orderedInterval (196905032839576402871316654099911 / 4000000000000000000000000000000000) (4922625820989430565584626747910931 / 100000000000000000000000000000000000))

theorem besselGridState048_step : besselStateSubset
    (besselIntervalStep (47 * 157 / 50) (157 / 50) 29 besselGridState047) besselGridState048 = true := by
  norm_num [besselGridState047, besselGridState048, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState048_valid : BesselStateValid (48 * 157 / 50 : ℚ) besselGridState048 := by
  have hv := besselIntervalStep_valid (47 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState047 besselGridState047_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (47 * 157 / 50) (157 / 50) 29 besselGridState047)
    (T := besselGridState048) besselGridState048_step hv
  convert hm using 1 <;> norm_num

def besselGridState049 : IntervalRat × IntervalRat :=
  (orderedInterval (-2088004625624721254263591197731539 / 50000000000000000000000000000000000) (-1044002312812355420770998486908329 / 25000000000000000000000000000000000),
   orderedInterval (-2439515055534986822274498415053863 / 50000000000000000000000000000000000) (-2439515055534976358898623034261147 / 50000000000000000000000000000000000))

theorem besselGridState049_step : besselStateSubset
    (besselIntervalStep (48 * 157 / 50) (157 / 50) 29 besselGridState048) besselGridState049 = true := by
  norm_num [besselGridState048, besselGridState049, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState049_valid : BesselStateValid (49 * 157 / 50 : ℚ) besselGridState049 := by
  have hv := besselIntervalStep_valid (48 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState048 besselGridState048_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (48 * 157 / 50) (157 / 50) 29 besselGridState048)
    (T := besselGridState049) besselGridState049_step hv
  convert hm using 1 <;> norm_num

def besselGridState050 : IntervalRat × IntervalRat :=
  (orderedInterval (2063199186524050593239437355307603 / 50000000000000000000000000000000000) (412639837304812244504508599840061 / 10000000000000000000000000000000000),
   orderedInterval (4836796828267024121052286024616561 / 100000000000000000000000000000000000) (4836796828267045481296473396421517 / 100000000000000000000000000000000000))

theorem besselGridState050_step : besselStateSubset
    (besselIntervalStep (49 * 157 / 50) (157 / 50) 29 besselGridState049) besselGridState050 = true := by
  norm_num [besselGridState049, besselGridState050, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState050_valid : BesselStateValid (50 * 157 / 50 : ℚ) besselGridState050 := by
  have hv := besselIntervalStep_valid (49 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState049 besselGridState049_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (49 * 157 / 50) (157 / 50) 29 besselGridState049)
    (T := besselGridState050) besselGridState050_step hv
  convert hm using 1 <;> norm_num

def besselGridState051 : IntervalRat × IntervalRat :=
  (orderedInterval (-2039082683917652403829823190822113 / 50000000000000000000000000000000000) (-815633073567056623083476230708499 / 20000000000000000000000000000000000),
   orderedInterval (-2397929130954553821799245620511047 / 50000000000000000000000000000000000) (-479585826190908584931819619803141 / 10000000000000000000000000000000000))

theorem besselGridState051_step : besselStateSubset
    (besselIntervalStep (50 * 157 / 50) (157 / 50) 29 besselGridState050) besselGridState051 = true := by
  norm_num [besselGridState050, besselGridState051, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState051_valid : BesselStateValid (51 * 157 / 50 : ℚ) besselGridState051 := by
  have hv := besselIntervalStep_valid (50 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState050 besselGridState050_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (50 * 157 / 50) (157 / 50) 29 besselGridState050)
    (T := besselGridState051) besselGridState051_step hv
  convert hm using 1 <;> norm_num

def besselGridState052 : IntervalRat × IntervalRat :=
  (orderedInterval (403124432319706098873202576750133 / 10000000000000000000000000000000000) (2015622161598541557602086322301561 / 50000000000000000000000000000000000),
   orderedInterval (237807564086236756976089632312971 / 5000000000000000000000000000000000) (2378075640862378684191553847196613 / 50000000000000000000000000000000000))

theorem besselGridState052_step : besselStateSubset
    (besselIntervalStep (51 * 157 / 50) (157 / 50) 29 besselGridState051) besselGridState052 = true := by
  norm_num [besselGridState051, besselGridState052, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState052_valid : BesselStateValid (52 * 157 / 50 : ℚ) besselGridState052 := by
  have hv := besselIntervalStep_valid (51 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState051 besselGridState051_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (51 * 157 / 50) (157 / 50) 29 besselGridState051)
    (T := besselGridState052) besselGridState052_step hv
  convert hm using 1 <;> norm_num

def besselGridState053 : IntervalRat × IntervalRat :=
  (orderedInterval (-3985573676222374775815097029153941 / 100000000000000000000000000000000000) (-996393419055588053639611447023527 / 25000000000000000000000000000000000),
   orderedInterval (-2358808473918305101788729527980733 / 50000000000000000000000000000000000) (-2358808473918293769794500509759979 / 50000000000000000000000000000000000))

theorem besselGridState053_step : besselStateSubset
    (besselIntervalStep (52 * 157 / 50) (157 / 50) 29 besselGridState052) besselGridState053 = true := by
  norm_num [besselGridState052, besselGridState053, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState053_valid : BesselStateValid (53 * 157 / 50 : ℚ) besselGridState053 := by
  have hv := besselIntervalStep_valid (52 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState052 besselGridState052_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (52 * 157 / 50) (157 / 50) 29 besselGridState052)
    (T := besselGridState053) besselGridState053_step hv
  convert hm using 1 <;> norm_num

def besselGridState054 : IntervalRat × IntervalRat :=
  (orderedInterval (492636981341915816211981737947851 / 12500000000000000000000000000000000) (3941095850735349526292425854075737 / 100000000000000000000000000000000000),
   orderedInterval (2340100080276267382049627559427321 / 50000000000000000000000000000000000) (2340100080276278931881080888422041 / 50000000000000000000000000000000000))

theorem besselGridState054_step : besselStateSubset
    (besselIntervalStep (53 * 157 / 50) (157 / 50) 29 besselGridState053) besselGridState054 = true := by
  norm_num [besselGridState053, besselGridState054, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState054_valid : BesselStateValid (54 * 157 / 50 : ℚ) besselGridState054 := by
  have hv := besselIntervalStep_valid (53 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState053 besselGridState053_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (53 * 157 / 50) (157 / 50) 29 besselGridState053)
    (T := besselGridState054) besselGridState054_step hv
  convert hm using 1 <;> norm_num

def besselGridState055 : IntervalRat × IntervalRat :=
  (orderedInterval (-389775693086356142920019725020337 / 10000000000000000000000000000000000) (-1948878465431768998353747893121287 / 50000000000000000000000000000000000),
   orderedInterval (-290240584077790303478320786688069 / 6250000000000000000000000000000000) (-2321924672622310659883657329692789 / 50000000000000000000000000000000000))

theorem besselGridState055_step : besselStateSubset
    (besselIntervalStep (54 * 157 / 50) (157 / 50) 29 besselGridState054) besselGridState055 = true := by
  norm_num [besselGridState054, besselGridState055, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState055_valid : BesselStateValid (55 * 157 / 50 : ℚ) besselGridState055 := by
  have hv := besselIntervalStep_valid (54 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState054 besselGridState054_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (54 * 157 / 50) (157 / 50) 29 besselGridState054)
    (T := besselGridState055) besselGridState055_step hv
  convert hm using 1 <;> norm_num

def besselGridState056 : IntervalRat × IntervalRat :=
  (orderedInterval (385550636671565778789297812451331 / 10000000000000000000000000000000000) (3855506366715681656838809376492671 / 100000000000000000000000000000000000),
   orderedInterval (2304258084118613295483787043058337 / 50000000000000000000000000000000000) (4608516168237250563625899444336989 / 100000000000000000000000000000000000))

theorem besselGridState056_step : besselStateSubset
    (besselIntervalStep (55 * 157 / 50) (157 / 50) 29 besselGridState055) besselGridState056 = true := by
  norm_num [besselGridState055, besselGridState056, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState056_valid : BesselStateValid (56 * 157 / 50 : ℚ) besselGridState056 := by
  have hv := besselIntervalStep_valid (55 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState055 besselGridState055_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (55 * 157 / 50) (157 / 50) 29 besselGridState055)
    (T := besselGridState056) besselGridState056_step hv
  convert hm using 1 <;> norm_num

def besselGridState057 : IntervalRat × IntervalRat :=
  (orderedInterval (-476787088562506529379596487534139 / 12500000000000000000000000000000000) (-3814296708500027929080019936961189 / 100000000000000000000000000000000000),
   orderedInterval (-2287077640081730951884016187005619 / 50000000000000000000000000000000000) (-914831056032687498757298296907957 / 20000000000000000000000000000000000))

theorem besselGridState057_step : besselStateSubset
    (besselIntervalStep (56 * 157 / 50) (157 / 50) 29 besselGridState056) besselGridState057 = true := by
  norm_num [besselGridState056, besselGridState057, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState057_valid : BesselStateValid (57 * 157 / 50 : ℚ) besselGridState057 := by
  have hv := besselIntervalStep_valid (56 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState056 besselGridState056_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (56 * 157 / 50) (157 / 50) 29 besselGridState056)
    (T := besselGridState057) besselGridState057_step hv
  convert hm using 1 <;> norm_num

def besselGridState058 : IntervalRat × IntervalRat :=
  (orderedInterval (3774083365890706915693873538742419 / 100000000000000000000000000000000000) (754816673178146331844025422870467 / 20000000000000000000000000000000000),
   orderedInterval (227036204185344929170010478971067 / 5000000000000000000000000000000000) (283795255231682714453547888400699 / 6250000000000000000000000000000000))

theorem besselGridState058_step : besselStateSubset
    (besselIntervalStep (57 * 157 / 50) (157 / 50) 29 besselGridState057) besselGridState058 = true := by
  norm_num [besselGridState057, besselGridState058, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState058_valid : BesselStateValid (58 * 157 / 50 : ℚ) besselGridState058 := by
  have hv := besselIntervalStep_valid (57 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState057 besselGridState057_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (57 * 157 / 50) (157 / 50) 29 besselGridState057)
    (T := besselGridState058) besselGridState058_step hv
  convert hm using 1 <;> norm_num

def besselGridState059 : IntervalRat × IntervalRat :=
  (orderedInterval (-3734824389854497251584423707263677 / 100000000000000000000000000000000000) (-466853048731809008741162271892293 / 12500000000000000000000000000000000),
   orderedInterval (-2254091261519376989811939749356947 / 50000000000000000000000000000000000) (-70440351922480135833428641110369 / 1562500000000000000000000000000000))

theorem besselGridState059_step : besselStateSubset
    (besselIntervalStep (58 * 157 / 50) (157 / 50) 29 besselGridState058) besselGridState059 = true := by
  norm_num [besselGridState058, besselGridState059, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState059_valid : BesselStateValid (59 * 157 / 50 : ℚ) besselGridState059 := by
  have hv := besselIntervalStep_valid (58 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState058 besselGridState058_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (58 * 157 / 50) (157 / 50) 29 besselGridState058)
    (T := besselGridState059) besselGridState059_step hv
  convert hm using 1 <;> norm_num

def besselGridState060 : IntervalRat × IntervalRat :=
  (orderedInterval (115515008578164924318073010729017 / 3125000000000000000000000000000000) (462060034312662899815311651166349 / 12500000000000000000000000000000000),
   orderedInterval (4476492892595769424511476662409939 / 100000000000000000000000000000000000) (895298578519159029955548824601899 / 20000000000000000000000000000000000))

theorem besselGridState060_step : besselStateSubset
    (besselIntervalStep (59 * 157 / 50) (157 / 50) 29 besselGridState059) besselGridState060 = true := by
  norm_num [besselGridState059, besselGridState060, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState060_valid : BesselStateValid (60 * 157 / 50 : ℚ) besselGridState060 := by
  have hv := besselIntervalStep_valid (59 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState059 besselGridState059_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (59 * 157 / 50) (157 / 50) 29 besselGridState059)
    (T := besselGridState060) besselGridState060_step hv
  convert hm using 1 <;> norm_num

def besselGridState061 : IntervalRat × IntervalRat :=
  (orderedInterval (-457376722102622996855999234119187 / 12500000000000000000000000000000000) (-1829506888410478957626928779741749 / 50000000000000000000000000000000000),
   orderedInterval (-11114049157840442157912499250129 / 250000000000000000000000000000000) (-555702457892018837295242312601797 / 12500000000000000000000000000000000))

theorem besselGridState061_step : besselStateSubset
    (besselIntervalStep (60 * 157 / 50) (157 / 50) 29 besselGridState060) besselGridState061 = true := by
  norm_num [besselGridState060, besselGridState061, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState061_valid : BesselStateValid (61 * 157 / 50 : ℚ) besselGridState061 := by
  have hv := besselIntervalStep_valid (60 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState060 besselGridState060_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (60 * 157 / 50) (157 / 50) 29 besselGridState060)
    (T := besselGridState061) besselGridState061_step hv
  convert hm using 1 <;> norm_num

def besselGridState062 : IntervalRat × IntervalRat :=
  (orderedInterval (1811194876213999865662846240585643 / 50000000000000000000000000000000000) (3622389752428026230731544898272321 / 100000000000000000000000000000000000),
   orderedInterval (4415529323258122548326768986327989 / 100000000000000000000000000000000000) (1103882330814537288305655990988367 / 25000000000000000000000000000000000))

theorem besselGridState062_step : besselStateSubset
    (besselIntervalStep (61 * 157 / 50) (157 / 50) 29 besselGridState061) besselGridState062 = true := by
  norm_num [besselGridState061, besselGridState062, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState062_valid : BesselStateValid (62 * 157 / 50 : ℚ) besselGridState062 := by
  have hv := besselIntervalStep_valid (61 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState061 besselGridState061_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (61 * 157 / 50) (157 / 50) 29 besselGridState061)
    (T := besselGridState062) besselGridState062_step hv
  convert hm using 1 <;> norm_num

def besselGridState063 : IntervalRat × IntervalRat :=
  (orderedInterval (-1793287502830121752816979795814779 / 50000000000000000000000000000000000) (-896643751415054141463466492867809 / 25000000000000000000000000000000000),
   orderedInterval (-1096547558696084234435495622800853 / 25000000000000000000000000000000000) (-877238046956861978439263920002309 / 20000000000000000000000000000000000))

theorem besselGridState063_step : besselStateSubset
    (besselIntervalStep (62 * 157 / 50) (157 / 50) 29 besselGridState062) besselGridState063 = true := by
  norm_num [besselGridState062, besselGridState063, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState063_valid : BesselStateValid (63 * 157 / 50 : ℚ) besselGridState063 := by
  have hv := besselIntervalStep_valid (62 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState062 besselGridState062_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (62 * 157 / 50) (157 / 50) 29 besselGridState062)
    (T := besselGridState063) besselGridState063_step hv
  convert hm using 1 <;> norm_num

def besselGridState064 : IntervalRat × IntervalRat :=
  (orderedInterval (221971134535709996269990302270467 / 6250000000000000000000000000000000) (355153815257138732103749318926479 / 10000000000000000000000000000000000),
   orderedInterval (4357572500601012796175191958779403 / 100000000000000000000000000000000000) (2178786250300520141464339397491897 / 50000000000000000000000000000000000))

theorem besselGridState064_step : besselStateSubset
    (besselIntervalStep (63 * 157 / 50) (157 / 50) 29 besselGridState063) besselGridState064 = true := by
  norm_num [besselGridState063, besselGridState064, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState064_valid : BesselStateValid (64 * 157 / 50 : ℚ) besselGridState064 := by
  have hv := besselIntervalStep_valid (63 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState063 besselGridState063_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (63 * 157 / 50) (157 / 50) 29 besselGridState063)
    (T := besselGridState064) besselGridState064_step hv
  convert hm using 1 <;> norm_num

def besselGridState065 : IntervalRat × IntervalRat :=
  (orderedInterval (-1758624747763240881653285321633919 / 50000000000000000000000000000000000) (-3517249495526453941087265531364453 / 100000000000000000000000000000000000),
   orderedInterval (-2164823921852565319028532408508169 / 50000000000000000000000000000000000) (-2164823921852551354768373695860711 / 50000000000000000000000000000000000))

theorem besselGridState065_step : besselStateSubset
    (besselIntervalStep (64 * 157 / 50) (157 / 50) 29 besselGridState064) besselGridState065 = true := by
  norm_num [besselGridState064, besselGridState065, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState065_valid : BesselStateValid (65 * 157 / 50 : ℚ) besselGridState065 := by
  have hv := besselIntervalStep_valid (64 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState064 besselGridState064_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (64 * 157 / 50) (157 / 50) 29 besselGridState064)
    (T := besselGridState065) besselGridState065_step hv
  convert hm using 1 <;> norm_num

def besselGridState066 : IntervalRat × IntervalRat :=
  (orderedInterval (3483680908255618611904769064703601 / 100000000000000000000000000000000000) (3483680908255646876190621597038233 / 100000000000000000000000000000000000),
   orderedInterval (430238949635299004913141187123529 / 10000000000000000000000000000000000) (1075597374088254604994636674623181 / 25000000000000000000000000000000000))

theorem besselGridState066_step : besselStateSubset
    (besselIntervalStep (65 * 157 / 50) (157 / 50) 29 besselGridState065) besselGridState066 = true := by
  norm_num [besselGridState065, besselGridState066, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState066_valid : BesselStateValid (66 * 157 / 50 : ℚ) besselGridState066 := by
  have hv := besselIntervalStep_valid (65 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState065 besselGridState065_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (65 * 157 / 50) (157 / 50) 29 besselGridState065)
    (T := besselGridState066) besselGridState066_step hv
  convert hm using 1 <;> norm_num

def besselGridState067 : IntervalRat × IntervalRat :=
  (orderedInterval (-3450805730350472883937353386538637 / 100000000000000000000000000000000000) (-431350716293805522127409241429723 / 12500000000000000000000000000000000),
   orderedInterval (-855154419666013913241475191823183 / 20000000000000000000000000000000000) (-2137886049165020376236233210342471 / 50000000000000000000000000000000000))

theorem besselGridState067_step : besselStateSubset
    (besselIntervalStep (66 * 157 / 50) (157 / 50) 29 besselGridState066) besselGridState067 = true := by
  norm_num [besselGridState066, besselGridState067, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState067_valid : BesselStateValid (67 * 157 / 50 : ℚ) besselGridState067 := by
  have hv := besselIntervalStep_valid (66 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState066 besselGridState066_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (66 * 157 / 50) (157 / 50) 29 besselGridState066)
    (T := besselGridState067) besselGridState067_step hv
  convert hm using 1 <;> norm_num

def besselGridState068 : IntervalRat × IntervalRat :=
  (orderedInterval (3418598670299208422110152552538129 / 100000000000000000000000000000000000) (3418598670299237572226927540677917 / 100000000000000000000000000000000000),
   orderedInterval (1062442900866804720057683168984037 / 25000000000000000000000000000000000) (4249771603467248137415335768110491 / 100000000000000000000000000000000000))

theorem besselGridState068_step : besselStateSubset
    (besselIntervalStep (67 * 157 / 50) (157 / 50) 29 besselGridState067) besselGridState068 = true := by
  norm_num [besselGridState067, besselGridState068, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState068_valid : BesselStateValid (68 * 157 / 50 : ℚ) besselGridState068 := by
  have hv := besselIntervalStep_valid (67 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState067 besselGridState067_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (67 * 157 / 50) (157 / 50) 29 besselGridState067)
    (T := besselGridState068) besselGridState068_step hv
  convert hm using 1 <;> norm_num

def besselGridState069 : IntervalRat × IntervalRat :=
  (orderedInterval (-338703571625563940409568764968881 / 10000000000000000000000000000000000) (-16935178581278049051064795432789 / 500000000000000000000000000000000),
   orderedInterval (-2112182596813397447506835526464257 / 50000000000000000000000000000000000) (-2112182596813382596908251170346381 / 50000000000000000000000000000000000))

theorem besselGridState069_step : besselStateSubset
    (besselIntervalStep (68 * 157 / 50) (157 / 50) 29 besselGridState068) besselGridState069 = true := by
  norm_num [besselGridState068, besselGridState069, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState069_valid : BesselStateValid (69 * 157 / 50 : ℚ) besselGridState069 := by
  have hv := besselIntervalStep_valid (68 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState068 besselGridState068_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (68 * 157 / 50) (157 / 50) 29 besselGridState068)
    (T := besselGridState069) besselGridState069_step hv
  convert hm using 1 <;> norm_num

def besselGridState070 : IntervalRat × IntervalRat :=
  (orderedInterval (1678047026911051160295396557046861 / 50000000000000000000000000000000000) (104877939181941636212735096934623 / 3125000000000000000000000000000000),
   orderedInterval (4199531199462203376211884739519141 / 100000000000000000000000000000000000) (4199531199462233521985436654720493 / 100000000000000000000000000000000000))

theorem besselGridState070_step : besselStateSubset
    (besselIntervalStep (69 * 157 / 50) (157 / 50) 29 besselGridState069) besselGridState070 = true := by
  norm_num [besselGridState069, besselGridState070, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState070_valid : BesselStateValid (70 * 157 / 50 : ℚ) besselGridState070 := by
  have hv := besselIntervalStep_valid (69 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState069 besselGridState069_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (69 * 157 / 50) (157 / 50) 29 besselGridState069)
    (T := besselGridState070) besselGridState070_step hv
  convert hm using 1 <;> norm_num

def besselGridState071 : IntervalRat × IntervalRat :=
  (orderedInterval (-1662875995102499608196185491029403 / 50000000000000000000000000000000000) (-831437997551242183318200371926821 / 25000000000000000000000000000000000),
   orderedInterval (-4175249027331473631888214123193131 / 100000000000000000000000000000000000) (-521906128416430380121690382066443 / 12500000000000000000000000000000000))

theorem besselGridState071_step : besselStateSubset
    (besselIntervalStep (70 * 157 / 50) (157 / 50) 29 besselGridState070) besselGridState071 = true := by
  norm_num [besselGridState070, besselGridState071, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState071_valid : BesselStateValid (71 * 157 / 50 : ℚ) besselGridState071 := by
  have hv := besselIntervalStep_valid (70 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState070 besselGridState070_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (70 * 157 / 50) (157 / 50) 29 besselGridState070)
    (T := besselGridState071) besselGridState071_step hv
  convert hm using 1 <;> norm_num

def besselGridState072 : IntervalRat × IntervalRat :=
  (orderedInterval (1647994442082663455632093345697237 / 50000000000000000000000000000000000) (25749913157541858123876753714737 / 781250000000000000000000000000000),
   orderedInterval (2075749545903271491868308050018609 / 50000000000000000000000000000000000) (4151499091806574020358133995290369 / 100000000000000000000000000000000000))

theorem besselGridState072_step : besselStateSubset
    (besselIntervalStep (71 * 157 / 50) (157 / 50) 29 besselGridState071) besselGridState072 = true := by
  norm_num [besselGridState071, besselGridState072, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState072_valid : BesselStateValid (72 * 157 / 50 : ℚ) besselGridState072 := by
  have hv := besselIntervalStep_valid (71 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState071 besselGridState071_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (71 * 157 / 50) (157 / 50) 29 besselGridState071)
    (T := besselGridState072) besselGridState072_step hv
  convert hm using 1 <;> norm_num

def besselGridState073 : IntervalRat × IntervalRat :=
  (orderedInterval (-3266785081249532306994631994088741 / 100000000000000000000000000000000000) (-3266785081249500932359705925030073 / 100000000000000000000000000000000000),
   orderedInterval (-412826275328097169891703354766837 / 10000000000000000000000000000000000) (-4128262753280940216022075579359301 / 100000000000000000000000000000000000))

theorem besselGridState073_step : besselStateSubset
    (besselIntervalStep (72 * 157 / 50) (157 / 50) 29 besselGridState072) besselGridState073 = true := by
  norm_num [besselGridState072, besselGridState073, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState073_valid : BesselStateValid (73 * 157 / 50 : ℚ) besselGridState073 := by
  have hv := besselIntervalStep_valid (72 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState072 besselGridState072_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (72 * 157 / 50) (157 / 50) 29 besselGridState072)
    (T := besselGridState073) besselGridState073_step hv
  convert hm using 1 <;> norm_num

def besselGridState074 : IntervalRat × IntervalRat :=
  (orderedInterval (3238121853834611410602674789842109 / 100000000000000000000000000000000000) (3238121853834643231851700900291787 / 100000000000000000000000000000000000),
   orderedInterval (821104452045122108083046600832369 / 20000000000000000000000000000000000) (2052761130112821235075582068317323 / 50000000000000000000000000000000000))

theorem besselGridState074_step : besselStateSubset
    (besselIntervalStep (73 * 157 / 50) (157 / 50) 29 besselGridState073) besselGridState074 = true := by
  norm_num [besselGridState073, besselGridState074, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState074_valid : BesselStateValid (74 * 157 / 50 : ℚ) besselGridState074 := by
  have hv := besselIntervalStep_valid (73 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState073 besselGridState073_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (73 * 157 / 50) (157 / 50) 29 besselGridState073)
    (T := besselGridState074) besselGridState074_step hv
  convert hm using 1 <;> norm_num

def besselGridState075 : IntervalRat × IntervalRat :=
  (orderedInterval (-3209981345571743954180465221317881 / 100000000000000000000000000000000000) (-3209981345571711685745334966909221 / 100000000000000000000000000000000000),
   orderedInterval (-4083260695690571566845459880128927 / 100000000000000000000000000000000000) (-2041630347845269594850053978915387 / 50000000000000000000000000000000000))

theorem besselGridState075_step : besselStateSubset
    (besselIntervalStep (74 * 157 / 50) (157 / 50) 29 besselGridState074) besselGridState075 = true := by
  norm_num [besselGridState074, besselGridState075, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState075_valid : BesselStateValid (75 * 157 / 50 : ℚ) besselGridState075 := by
  have hv := besselIntervalStep_valid (74 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState074 besselGridState074_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (74 * 157 / 50) (157 / 50) 29 besselGridState074)
    (T := besselGridState075) besselGridState075_step hv
  convert hm using 1 <;> norm_num

def besselGridState076 : IntervalRat × IntervalRat :=
  (orderedInterval (31823465198500637379297562323731 / 1000000000000000000000000000000000) (198896657490631028382736731104777 / 6250000000000000000000000000000000),
   orderedInterval (507682740960970550907277243438327 / 12500000000000000000000000000000000) (1015365481921949308095586971766621 / 25000000000000000000000000000000000))

theorem besselGridState076_step : besselStateSubset
    (besselIntervalStep (75 * 157 / 50) (157 / 50) 29 besselGridState075) besselGridState076 = true := by
  norm_num [besselGridState075, besselGridState076, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState076_valid : BesselStateValid (76 * 157 / 50 : ℚ) besselGridState076 := by
  have hv := besselIntervalStep_valid (75 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState075 besselGridState075_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (75 * 157 / 50) (157 / 50) 29 besselGridState075)
    (T := besselGridState076) besselGridState076_step hv
  convert hm using 1 <;> norm_num

def besselGridState077 : IntervalRat × IntervalRat :=
  (orderedInterval (-3155201111942886093230430136645981 / 100000000000000000000000000000000000) (-1577600555971426464351953389962557 / 50000000000000000000000000000000000),
   orderedInterval (-4040110563127766989532066043135503 / 100000000000000000000000000000000000) (-2020055281563866857929447918699977 / 50000000000000000000000000000000000))

theorem besselGridState077_step : besselStateSubset
    (besselIntervalStep (76 * 157 / 50) (157 / 50) 29 besselGridState076) besselGridState077 = true := by
  norm_num [besselGridState076, besselGridState077, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState077_valid : BesselStateValid (77 * 157 / 50 : ℚ) besselGridState077 := by
  have hv := besselIntervalStep_valid (76 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState076 besselGridState076_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (76 * 157 / 50) (157 / 50) 29 besselGridState076)
    (T := besselGridState077) besselGridState077_step hv
  convert hm using 1 <;> norm_num

def besselGridState078 : IntervalRat × IntervalRat :=
  (orderedInterval (782132396131835116987204212487449 / 25000000000000000000000000000000000) (1564264792263687040691108535160939 / 50000000000000000000000000000000000),
   orderedInterval (200959595250615964183933991558323 / 5000000000000000000000000000000000) (1004797976253088251618013330262609 / 25000000000000000000000000000000000))

theorem besselGridState078_step : besselStateSubset
    (besselIntervalStep (77 * 157 / 50) (157 / 50) 29 besselGridState077) besselGridState078 = true := by
  norm_num [besselGridState077, besselGridState078, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState078_valid : BesselStateValid (78 * 157 / 50 : ℚ) besselGridState078 := by
  have hv := besselIntervalStep_valid (77 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState077 besselGridState077_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (77 * 157 / 50) (157 / 50) 29 besselGridState077)
    (T := besselGridState078) besselGridState078_step hv
  convert hm using 1 <;> norm_num

def besselGridState079 : IntervalRat × IntervalRat :=
  (orderedInterval (-1551158543150831662524487625385239 / 50000000000000000000000000000000000) (-3102317086301629262133518197693229 / 100000000000000000000000000000000000),
   orderedInterval (-499836489077009404549878415427547 / 12500000000000000000000000000000000) (-1999345956308020531956695354742901 / 50000000000000000000000000000000000))

theorem besselGridState079_step : besselStateSubset
    (besselIntervalStep (78 * 157 / 50) (157 / 50) 29 besselGridState078) besselGridState079 = true := by
  norm_num [besselGridState078, besselGridState079, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState079_valid : BesselStateValid (79 * 157 / 50 : ℚ) besselGridState079 := by
  have hv := besselIntervalStep_valid (78 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState078 besselGridState078_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (78 * 157 / 50) (157 / 50) 29 besselGridState078)
    (T := besselGridState079) besselGridState079_step hv
  convert hm using 1 <;> norm_num

def besselGridState080 : IntervalRat × IntervalRat :=
  (orderedInterval (615309882689258299400271792886061 / 20000000000000000000000000000000000) (1538274706723163004987424273210263 / 50000000000000000000000000000000000),
   orderedInterval (1989298582206124444044678168543489 / 50000000000000000000000000000000000) (3978597164412283510840209074301683 / 100000000000000000000000000000000000))

theorem besselGridState080_step : besselStateSubset
    (besselIntervalStep (79 * 157 / 50) (157 / 50) 29 besselGridState079) besselGridState080 = true := by
  norm_num [besselGridState079, besselGridState080, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState080_valid : BesselStateValid (80 * 157 / 50 : ℚ) besselGridState080 := by
  have hv := besselIntervalStep_valid (79 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState079 besselGridState079_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (79 * 157 / 50) (157 / 50) 29 besselGridState079)
    (T := besselGridState080) besselGridState080_step hv
  convert hm using 1 <;> norm_num

def besselGridState081 : IntervalRat × IntervalRat :=
  (orderedInterval (-1525606486851237248075678115916013 / 50000000000000000000000000000000000) (-3051212973702439532543061943628931 / 100000000000000000000000000000000000),
   orderedInterval (-1979447411761802322874295558766011 / 50000000000000000000000000000000000) (-494861852940446196519834936957367 / 12500000000000000000000000000000000))

theorem besselGridState081_step : besselStateSubset
    (besselIntervalStep (80 * 157 / 50) (157 / 50) 29 besselGridState080) besselGridState081 = true := by
  norm_num [besselGridState080, besselGridState081, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState081_valid : BesselStateValid (81 * 157 / 50 : ℚ) besselGridState081 := by
  have hv := besselIntervalStep_valid (80 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState080 besselGridState080_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (80 * 157 / 50) (157 / 50) 29 besselGridState080)
    (T := besselGridState081) besselGridState081_step hv
  convert hm using 1 <;> norm_num

def besselGridState082 : IntervalRat × IntervalRat :=
  (orderedInterval (378286844107341658467600413997911 / 12500000000000000000000000000000000) (756573688214692170640367935210963 / 25000000000000000000000000000000000),
   orderedInterval (3939572605496139362678899221007699 / 100000000000000000000000000000000000) (3939572605496174887682599101714281 / 100000000000000000000000000000000000))

theorem besselGridState082_step : besselStateSubset
    (besselIntervalStep (81 * 157 / 50) (157 / 50) 29 besselGridState081) besselGridState082 = true := by
  norm_num [besselGridState081, besselGridState082, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState082_valid : BesselStateValid (82 * 157 / 50 : ℚ) besselGridState082 := by
  have hv := besselIntervalStep_valid (81 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState081 besselGridState081_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (81 * 157 / 50) (157 / 50) 29 besselGridState081)
    (T := besselGridState082) besselGridState082_step hv
  convert hm using 1 <;> norm_num

def besselGridState083 : IntervalRat × IntervalRat :=
  (orderedInterval (-750445570864655123271068644887873 / 25000000000000000000000000000000000) (-3001782283458584626472864521650039 / 100000000000000000000000000000000000),
   orderedInterval (-980154687053829957536554641652901 / 25000000000000000000000000000000000) (-1960309374107641926576558678924789 / 50000000000000000000000000000000000))

theorem besselGridState083_step : besselStateSubset
    (besselIntervalStep (82 * 157 / 50) (157 / 50) 29 besselGridState082) besselGridState083 = true := by
  norm_num [besselGridState082, besselGridState083, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState083_valid : BesselStateValid (83 * 157 / 50 : ℚ) besselGridState083 := by
  have hv := besselIntervalStep_valid (82 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState082 besselGridState082_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (82 * 157 / 50) (157 / 50) 29 besselGridState082)
    (T := besselGridState083) besselGridState083_step hv
  convert hm using 1 <;> norm_num

def besselGridState084 : IntervalRat × IntervalRat :=
  (orderedInterval (2977663615555686036883564152483529 / 100000000000000000000000000000000000) (2977663615555722355864882198017959 / 100000000000000000000000000000000000),
   orderedInterval (975505495949152859847315122593353 / 25000000000000000000000000000000000) (780404396759329573789651418067241 / 20000000000000000000000000000000000))

theorem besselGridState084_step : besselStateSubset
    (besselIntervalStep (83 * 157 / 50) (157 / 50) 29 besselGridState083) besselGridState084 = true := by
  norm_num [besselGridState083, besselGridState084, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState084_valid : BesselStateValid (84 * 157 / 50 : ℚ) besselGridState084 := by
  have hv := besselIntervalStep_valid (83 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState083 besselGridState083_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (83 * 157 / 50) (157 / 50) 29 besselGridState083)
    (T := besselGridState084) besselGridState084_step hv
  convert hm using 1 <;> norm_num

def besselGridState085 : IntervalRat × IntervalRat :=
  (orderedInterval (-2953927289361204270833344386860401 / 100000000000000000000000000000000000) (-738481822340291874725538072578749 / 25000000000000000000000000000000000),
   orderedInterval (-3883771512301194939088916916249883 / 100000000000000000000000000000000000) (-1941885756150579028193326183174931 / 50000000000000000000000000000000000))

theorem besselGridState085_step : besselStateSubset
    (besselIntervalStep (84 * 157 / 50) (157 / 50) 29 besselGridState084) besselGridState085 = true := by
  norm_num [besselGridState084, besselGridState085, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState085_valid : BesselStateValid (85 * 157 / 50 : ℚ) besselGridState085 := by
  have hv := besselIntervalStep_valid (84 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState084 besselGridState084_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (84 * 157 / 50) (157 / 50) 29 besselGridState084)
    (T := besselGridState085) besselGridState085_step hv
  convert hm using 1 <;> norm_num

def besselGridState086 : IntervalRat × IntervalRat :=
  (orderedInterval (2930562309639362817530466952151577 / 100000000000000000000000000000000000) (117222492385576001719691988787089 / 4000000000000000000000000000000000),
   orderedInterval (386585697713644082488314122004441 / 10000000000000000000000000000000000) (483232122142059770163365308234229 / 12500000000000000000000000000000000))

theorem besselGridState086_step : besselStateSubset
    (besselIntervalStep (85 * 157 / 50) (157 / 50) 29 besselGridState085) besselGridState086 = true := by
  norm_num [besselGridState085, besselGridState086, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState086_valid : BesselStateValid (86 * 157 / 50 : ℚ) besselGridState086 := by
  have hv := besselIntervalStep_valid (85 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState085 besselGridState085_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (85 * 157 / 50) (157 / 50) 29 besselGridState085)
    (T := besselGridState086) besselGridState086_step hv
  convert hm using 1 <;> norm_num

def besselGridState087 : IntervalRat × IntervalRat :=
  (orderedInterval (-45430595651899088911137107661071 / 1562500000000000000000000000000000) (-1453779060860752005369366703603309 / 50000000000000000000000000000000000),
   orderedInterval (-384826844201724280229630551083513 / 10000000000000000000000000000000000) (-3848268442017205011571884766009883 / 100000000000000000000000000000000000))

theorem besselGridState087_step : besselStateSubset
    (besselIntervalStep (86 * 157 / 50) (157 / 50) 29 besselGridState086) besselGridState087 = true := by
  norm_num [besselGridState086, besselGridState087, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState087_valid : BesselStateValid (87 * 157 / 50 : ℚ) besselGridState087 := by
  have hv := besselIntervalStep_valid (86 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState086 besselGridState086_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (86 * 157 / 50) (157 / 50) 29 besselGridState086)
    (T := besselGridState087) besselGridState087_step hv
  convert hm using 1 <;> norm_num

def besselGridState088 : IntervalRat × IntervalRat :=
  (orderedInterval (2884904589017808350696708660157813 / 100000000000000000000000000000000000) (90153268406807702655166537856277 / 3125000000000000000000000000000000),
   orderedInterval (957749092342605525800061261758203 / 25000000000000000000000000000000000) (957749092342615087201325046998761 / 25000000000000000000000000000000000))

theorem besselGridState088_step : besselStateSubset
    (besselIntervalStep (87 * 157 / 50) (157 / 50) 29 besselGridState087) besselGridState088 = true := by
  norm_num [besselGridState087, besselGridState088, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState088_valid : BesselStateValid (88 * 157 / 50 : ℚ) besselGridState088 := by
  have hv := besselIntervalStep_valid (87 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState087 besselGridState087_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (87 * 157 / 50) (157 / 50) 29 besselGridState087)
    (T := besselGridState088) besselGridState088_step hv
  convert hm using 1 <;> norm_num

def besselGridState089 : IntervalRat × IntervalRat :=
  (orderedInterval (-89455999122454407709700679255729 / 3125000000000000000000000000000000) (-715647992979625614291012139618103 / 25000000000000000000000000000000000),
   orderedInterval (-953507900019719686066677399317929 / 25000000000000000000000000000000000) (-3814031600078840043200154874948443 / 100000000000000000000000000000000000))

theorem besselGridState089_step : besselStateSubset
    (besselIntervalStep (88 * 157 / 50) (157 / 50) 29 besselGridState088) besselGridState089 = true := by
  norm_num [besselGridState088, besselGridState089, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState089_valid : BesselStateValid (89 * 157 / 50 : ℚ) besselGridState089 := by
  have hv := besselIntervalStep_valid (88 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState088 besselGridState088_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (88 * 157 / 50) (157 / 50) 29 besselGridState088)
    (T := besselGridState089) besselGridState089_step hv
  convert hm using 1 <;> norm_num

def besselGridState090 : IntervalRat × IntervalRat :=
  (orderedInterval (2840610907983454930262509672063607 / 100000000000000000000000000000000000) (568122181596698795134122630356409 / 20000000000000000000000000000000000),
   orderedInterval (949341333616552155862206310838157 / 25000000000000000000000000000000000) (3797365334466247780558613361916997 / 100000000000000000000000000000000000))

theorem besselGridState090_step : besselStateSubset
    (besselIntervalStep (89 * 157 / 50) (157 / 50) 29 besselGridState089) besselGridState090 = true := by
  norm_num [besselGridState089, besselGridState090, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState090_valid : BesselStateValid (90 * 157 / 50 : ℚ) besselGridState090 := by
  have hv := besselIntervalStep_valid (89 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState089 besselGridState089_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (89 * 157 / 50) (157 / 50) 29 besselGridState089)
    (T := besselGridState090) besselGridState090_step hv
  convert hm using 1 <;> norm_num

def besselGridState091 : IntervalRat × IntervalRat :=
  (orderedInterval (-352369049166050284726771220185771 / 12500000000000000000000000000000000) (-2818952393328362775959553262634523 / 100000000000000000000000000000000000),
   orderedInterval (-1890494557217669775602943336953033 / 50000000000000000000000000000000000) (-3780989114435299937470264234197713 / 100000000000000000000000000000000000))

theorem besselGridState091_step : besselStateSubset
    (besselIntervalStep (90 * 157 / 50) (157 / 50) 29 besselGridState090) besselGridState091 = true := by
  norm_num [besselGridState090, besselGridState091, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState091_valid : BesselStateValid (91 * 157 / 50 : ℚ) besselGridState091 := by
  have hv := besselIntervalStep_valid (90 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState090 besselGridState090_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (90 * 157 / 50) (157 / 50) 29 besselGridState090)
    (T := besselGridState091) besselGridState091_step hv
  convert hm using 1 <;> norm_num

def besselGridState092 : IntervalRat × IntervalRat :=
  (orderedInterval (1398803882561472775216770443506329 / 50000000000000000000000000000000000) (2797607765122985509320259100321131 / 100000000000000000000000000000000000),
   orderedInterval (3764894806677100962302211258786921 / 100000000000000000000000000000000000) (3764894806677141033247134665571333 / 100000000000000000000000000000000000))

theorem besselGridState092_step : besselStateSubset
    (besselIntervalStep (91 * 157 / 50) (157 / 50) 29 besselGridState091) besselGridState092 = true := by
  norm_num [besselGridState091, besselGridState092, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState092_valid : BesselStateValid (92 * 157 / 50 : ℚ) besselGridState092 := by
  have hv := besselIntervalStep_valid (91 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState091 besselGridState091_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (91 * 157 / 50) (157 / 50) 29 besselGridState091)
    (T := besselGridState092) besselGridState092_step hv
  convert hm using 1 <;> norm_num

def besselGridState093 : IntervalRat × IntervalRat :=
  (orderedInterval (-1388284342561731691675121951677451 / 50000000000000000000000000000000000) (-2776568685123422966845028353852309 / 100000000000000000000000000000000000),
   orderedInterval (-937268646719047228627994738946967 / 25000000000000000000000000000000000) (-3749074586876148385773423480907039 / 100000000000000000000000000000000000))

theorem besselGridState093_step : besselStateSubset
    (besselIntervalStep (92 * 157 / 50) (157 / 50) 29 besselGridState092) besselGridState093 = true := by
  norm_num [besselGridState092, besselGridState093, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState093_valid : BesselStateValid (93 * 157 / 50 : ℚ) besselGridState093 := by
  have hv := besselIntervalStep_valid (92 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState092 besselGridState092_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (92 * 157 / 50) (157 / 50) 29 besselGridState092)
    (T := besselGridState093) besselGridState093_step hv
  convert hm using 1 <;> norm_num

def besselGridState094 : IntervalRat × IntervalRat :=
  (orderedInterval (1377913562083878078964320266354639 / 50000000000000000000000000000000000) (2755827124167797032639556925785981 / 100000000000000000000000000000000000),
   orderedInterval (58336264450671436236526327620791 / 1562500000000000000000000000000000) (746704184968602581251013383372791 / 20000000000000000000000000000000000))

theorem besselGridState094_step : besselStateSubset
    (besselIntervalStep (93 * 157 / 50) (157 / 50) 29 besselGridState093) besselGridState094 = true := by
  norm_num [besselGridState093, besselGridState094, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState094_valid : BesselStateValid (94 * 157 / 50 : ℚ) besselGridState094 := by
  have hv := besselIntervalStep_valid (93 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState093 besselGridState093_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (93 * 157 / 50) (157 / 50) 29 besselGridState093)
    (T := besselGridState094) besselGridState094_step hv
  convert hm using 1 <;> norm_num

def besselGridState095 : IntervalRat × IntervalRat :=
  (orderedInterval (-1367687673783911501279004189748159 / 50000000000000000000000000000000000) (-27353753475677816690533787801301 / 1000000000000000000000000000000000),
   orderedInterval (-3718226570510112731109692077675013 / 100000000000000000000000000000000000) (-371822657051007128502742698354469 / 10000000000000000000000000000000000))

theorem besselGridState095_step : besselStateSubset
    (besselIntervalStep (94 * 157 / 50) (157 / 50) 29 besselGridState094) besselGridState095 = true := by
  norm_num [besselGridState094, besselGridState095, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState095_valid : BesselStateValid (95 * 157 / 50 : ℚ) besselGridState095 := by
  have hv := besselIntervalStep_valid (94 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState094 besselGridState094_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (94 * 157 / 50) (157 / 50) 29 besselGridState094)
    (T := besselGridState095) besselGridState095_step hv
  convert hm using 1 <;> norm_num

def besselGridState096 : IntervalRat × IntervalRat :=
  (orderedInterval (2715205901337515600834754919131513 / 100000000000000000000000000000000000) (1357602950668778696860959961241291 / 50000000000000000000000000000000000),
   orderedInterval (1851592270366413529818002326469983 / 50000000000000000000000000000000000) (1851592270366434482635035445059419 / 50000000000000000000000000000000000))

theorem besselGridState096_step : besselStateSubset
    (besselIntervalStep (95 * 157 / 50) (157 / 50) 29 besselGridState095) besselGridState096 = true := by
  norm_num [besselGridState095, besselGridState096, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState096_valid : BesselStateValid (96 * 157 / 50 : ℚ) besselGridState096 := by
  have hv := besselIntervalStep_valid (95 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState095 besselGridState095_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (95 * 157 / 50) (157 / 50) 29 besselGridState095)
    (T := besselGridState096) besselGridState096_step hv
  convert hm using 1 <;> norm_num

def besselGridState097 : IntervalRat × IntervalRat :=
  (orderedInterval (-16845697495010277806547974579671 / 625000000000000000000000000000000) (-1347655799600801098094171251808483 / 50000000000000000000000000000000000),
   orderedInterval (-1844194053420663194411381713184457 / 50000000000000000000000000000000000) (-368838810684128402304911756052781 / 10000000000000000000000000000000000))

theorem besselGridState097_step : besselStateSubset
    (besselIntervalStep (96 * 157 / 50) (157 / 50) 29 besselGridState096) besselGridState097 = true := by
  norm_num [besselGridState096, besselGridState097, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState097_valid : BesselStateValid (97 * 157 / 50 : ℚ) besselGridState097 := by
  have hv := besselIntervalStep_valid (96 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState096 besselGridState096_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (96 * 157 / 50) (157 / 50) 29 besselGridState096)
    (T := besselGridState097) besselGridState097_step hv
  convert hm using 1 <;> norm_num

def besselGridState098 : IntervalRat × IntervalRat :=
  (orderedInterval (21405484082657363032302378003591 / 800000000000000000000000000000000) (1337842755166106546229871974700559 / 50000000000000000000000000000000000),
   orderedInterval (734766156578577998374608030144803 / 20000000000000000000000000000000000) (367383078289293281837490387084349 / 10000000000000000000000000000000000))

theorem besselGridState098_step : besselStateSubset
    (besselIntervalStep (97 * 157 / 50) (157 / 50) 29 besselGridState097) besselGridState098 = true := by
  norm_num [besselGridState097, besselGridState098, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState098_valid : BesselStateValid (98 * 157 / 50 : ℚ) besselGridState098 := by
  have hv := besselIntervalStep_valid (97 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState097 besselGridState097_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (97 * 157 / 50) (157 / 50) 29 besselGridState097)
    (T := besselGridState098) besselGridState098_step hv
  convert hm using 1 <;> norm_num

def besselGridState099 : IntervalRat × IntervalRat :=
  (orderedInterval (-1328160473883162814759215715391323 / 50000000000000000000000000000000000) (-41505014808848163358478340452417 / 1562500000000000000000000000000000),
   orderedInterval (-91487657864502610604896184173901 / 2500000000000000000000000000000000) (-1829753157290030568188134243657611 / 50000000000000000000000000000000000))

theorem besselGridState099_step : besselStateSubset
    (besselIntervalStep (98 * 157 / 50) (157 / 50) 29 besselGridState098) besselGridState099 = true := by
  norm_num [besselGridState098, besselGridState099, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState099_valid : BesselStateValid (99 * 157 / 50 : ℚ) besselGridState099 := by
  have hv := besselIntervalStep_valid (98 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState098 besselGridState098_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (98 * 157 / 50) (157 / 50) 29 besselGridState098)
    (T := besselGridState099) besselGridState099_step hv
  convert hm using 1 <;> norm_num

def besselGridState100 : IntervalRat × IntervalRat :=
  (orderedInterval (1318605728729873208223894030960747 / 50000000000000000000000000000000000) (2637211457459790052769548163680159 / 100000000000000000000000000000000000),
   orderedInterval (1822704334374955201927355944452779 / 50000000000000000000000000000000000) (3645408668749954153582361735068479 / 100000000000000000000000000000000000))

theorem besselGridState100_step : besselStateSubset
    (besselIntervalStep (99 * 157 / 50) (157 / 50) 29 besselGridState099) besselGridState100 = true := by
  norm_num [besselGridState099, besselGridState100, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState100_valid : BesselStateValid (100 * 157 / 50 : ℚ) besselGridState100 := by
  have hv := besselIntervalStep_valid (99 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState099 besselGridState099_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (99 * 157 / 50) (157 / 50) 29 besselGridState099)
    (T := besselGridState100) besselGridState100_step hv
  convert hm using 1 <;> norm_num

def besselGridState101 : IntervalRat × IntervalRat :=
  (orderedInterval (-1309175403968196274532748755155807 / 50000000000000000000000000000000000) (-2618350807936348450404908564712339 / 100000000000000000000000000000000000),
   orderedInterval (-1815766011748346725505384629315377 / 50000000000000000000000000000000000) (-3631532023496649238783834636927281 / 100000000000000000000000000000000000))

theorem besselGridState101_step : besselStateSubset
    (besselIntervalStep (100 * 157 / 50) (157 / 50) 29 besselGridState100) besselGridState101 = true := by
  norm_num [besselGridState100, besselGridState101, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState101_valid : BesselStateValid (101 * 157 / 50 : ℚ) besselGridState101 := by
  have hv := besselIntervalStep_valid (100 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState100 besselGridState100_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (100 * 157 / 50) (157 / 50) 29 besselGridState100)
    (T := besselGridState101) besselGridState101_step hv
  convert hm using 1 <;> norm_num

def besselGridState102 : IntervalRat × IntervalRat :=
  (orderedInterval (2599732980494573478532324306423819 / 100000000000000000000000000000000000) (2599732980494618040125444377007301 / 100000000000000000000000000000000000),
   orderedInterval (904467689697520384654582472277953 / 25000000000000000000000000000000000) (452233844848765776742077583960131 / 12500000000000000000000000000000000))

theorem besselGridState102_step : besselStateSubset
    (besselIntervalStep (101 * 157 / 50) (157 / 50) 29 besselGridState101) besselGridState102 = true := by
  norm_num [besselGridState101, besselGridState102, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState102_valid : BesselStateValid (102 * 157 / 50 : ℚ) besselGridState102 := by
  have hv := besselIntervalStep_valid (101 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState101 besselGridState101_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (101 * 157 / 50) (157 / 50) 29 besselGridState101)
    (T := besselGridState102) besselGridState102_step hv
  convert hm using 1 <;> norm_num

def besselGridState103 : IntervalRat × IntervalRat :=
  (orderedInterval (-2581352159936689185643971438421787 / 100000000000000000000000000000000000) (-2581352159936644160523801026890213 / 100000000000000000000000000000000000),
   orderedInterval (-1802209723803161151282863326395171 / 50000000000000000000000000000000000) (-1802209723803138581781575551623591 / 50000000000000000000000000000000000))

theorem besselGridState103_step : besselStateSubset
    (besselIntervalStep (102 * 157 / 50) (157 / 50) 29 besselGridState102) besselGridState103 = true := by
  norm_num [besselGridState102, besselGridState103, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState103_valid : BesselStateValid (103 * 157 / 50 : ℚ) besselGridState103 := by
  have hv := besselIntervalStep_valid (102 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState102 besselGridState102_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (102 * 157 / 50) (157 / 50) 29 besselGridState102)
    (T := besselGridState103) besselGridState103_step hv
  convert hm using 1 <;> norm_num

def besselGridState104 : IntervalRat × IntervalRat :=
  (orderedInterval (2563202725787245480376527670782139 / 100000000000000000000000000000000000) (256320272578729096961908561854339 / 10000000000000000000000000000000000),
   orderedInterval (179558642376448115504248765338427 / 5000000000000000000000000000000000) (897793211882251978341405290309299 / 25000000000000000000000000000000000))

theorem besselGridState104_step : besselStateSubset
    (besselIntervalStep (103 * 157 / 50) (157 / 50) 29 besselGridState103) besselGridState104 = true := by
  norm_num [besselGridState103, besselGridState104, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState104_valid : BesselStateValid (104 * 157 / 50 : ℚ) besselGridState104 := by
  have hv := besselIntervalStep_valid (103 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState103 besselGridState103_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (103 * 157 / 50) (157 / 50) 29 besselGridState103)
    (T := besselGridState104) besselGridState104_step hv
  convert hm using 1 <;> norm_num

def besselGridState105 : IntervalRat × IntervalRat :=
  (orderedInterval (-2545279243971679229534743150020319 / 100000000000000000000000000000000000) (-1272639621985816637786820720150053 / 50000000000000000000000000000000000),
   orderedInterval (-1789062946396230755126670882815937 / 50000000000000000000000000000000000) (-894531473198103860524995840544667 / 25000000000000000000000000000000000))

theorem besselGridState105_step : besselStateSubset
    (besselIntervalStep (104 * 157 / 50) (157 / 50) 29 besselGridState104) besselGridState105 = true := by
  norm_num [besselGridState104, besselGridState105, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState105_valid : BesselStateValid (105 * 157 / 50 : ℚ) besselGridState105 := by
  have hv := besselIntervalStep_valid (104 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState104 besselGridState104_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (104 * 157 / 50) (157 / 50) 29 besselGridState104)
    (T := besselGridState105) besselGridState105_step hv
  convert hm using 1 <;> norm_num

def besselGridState106 : IntervalRat × IntervalRat :=
  (orderedInterval (157973528682810580104044651228239 / 6250000000000000000000000000000000) (2527576458925015700941336205009769 / 100000000000000000000000000000000000),
   orderedInterval (3565273686738728070196635290105983 / 100000000000000000000000000000000000) (3565273686738774603818205027003837 / 100000000000000000000000000000000000))

theorem besselGridState106_step : besselStateSubset
    (besselIntervalStep (105 * 157 / 50) (157 / 50) 29 besselGridState105) besselGridState106 = true := by
  norm_num [besselGridState105, besselGridState106, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState106_valid : BesselStateValid (106 * 157 / 50 : ℚ) besselGridState106 := by
  have hv := besselIntervalStep_valid (105 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState105 besselGridState105_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (105 * 157 / 50) (157 / 50) 29 besselGridState105)
    (T := besselGridState106) besselGridState106_step hv
  convert hm using 1 <;> norm_num

def besselGridState107 : IntervalRat × IntervalRat :=
  (orderedInterval (-1255044643053372976702159991142077 / 50000000000000000000000000000000000) (-251008928610669906821438065603127 / 10000000000000000000000000000000000),
   orderedInterval (-3552611494664242546893471377739821 / 100000000000000000000000000000000000) (-444076436833024443400916886399391 / 12500000000000000000000000000000000))

theorem besselGridState107_step : besselStateSubset
    (besselIntervalStep (106 * 157 / 50) (157 / 50) 29 besselGridState106) besselGridState107 = true := by
  norm_num [besselGridState106, besselGridState107, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState107_valid : BesselStateValid (107 * 157 / 50 : ℚ) besselGridState107 := by
  have hv := besselIntervalStep_valid (106 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState106 besselGridState106_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (106 * 157 / 50) (157 / 50) 29 besselGridState106)
    (T := besselGridState107) besselGridState107_step hv
  convert hm using 1 <;> norm_num

def besselGridState108 : IntervalRat × IntervalRat :=
  (orderedInterval (1246406402447803817869273638494251 / 50000000000000000000000000000000000) (498562560979130997488084766099709 / 20000000000000000000000000000000000),
   orderedInterval (3540134737031358713464600006574733 / 100000000000000000000000000000000000) (35401347370314061798125144362959 / 1000000000000000000000000000000000))

theorem besselGridState108_step : besselStateSubset
    (besselIntervalStep (107 * 157 / 50) (157 / 50) 29 besselGridState107) besselGridState108 = true := by
  norm_num [besselGridState107, besselGridState108, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState108_valid : BesselStateValid (108 * 157 / 50 : ℚ) besselGridState108 := by
  have hv := besselIntervalStep_valid (107 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState107 besselGridState107_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (107 * 157 / 50) (157 / 50) 29 besselGridState107)
    (T := besselGridState108) besselGridState108_step hv
  convert hm using 1 <;> norm_num

def besselGridState109 : IntervalRat × IntervalRat :=
  (orderedInterval (-2475742251842911799517789905286067 / 100000000000000000000000000000000000) (-1237871125921431990352266570921483 / 50000000000000000000000000000000000),
   orderedInterval (-705567796604976743535367836977811 / 20000000000000000000000000000000000) (-705567796604967156813815728788257 / 20000000000000000000000000000000000))

theorem besselGridState109_step : besselStateSubset
    (besselIntervalStep (108 * 157 / 50) (157 / 50) 29 besselGridState108) besselGridState109 = true := by
  norm_num [besselGridState108, besselGridState109, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState109_valid : BesselStateValid (109 * 157 / 50 : ℚ) besselGridState109 := by
  have hv := besselIntervalStep_valid (108 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState108 besselGridState108_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (108 * 157 / 50) (157 / 50) 29 besselGridState108)
    (T := besselGridState109) besselGridState109_step hv
  convert hm using 1 <;> norm_num

def besselGridState110 : IntervalRat × IntervalRat :=
  (orderedInterval (19209945423921194341638480548701 / 781250000000000000000000000000000) (614718253565490290563657460821939 / 25000000000000000000000000000000000),
   orderedInterval (1757859972215288589033885506607733 / 50000000000000000000000000000000000) (703143988886125115906860410855973 / 20000000000000000000000000000000000))

theorem besselGridState110_step : besselStateSubset
    (besselIntervalStep (109 * 157 / 50) (157 / 50) 29 besselGridState109) besselGridState110 = true := by
  norm_num [besselGridState109, besselGridState110, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState110_valid : BesselStateValid (110 * 157 / 50 : ℚ) besselGridState110 := by
  have hv := besselIntervalStep_valid (109 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState109 besselGridState109_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (109 * 157 / 50) (157 / 50) 29 besselGridState109)
    (T := besselGridState110) besselGridState110_step hv
  convert hm using 1 <;> norm_num

def besselGridState111 : IntervalRat × IntervalRat :=
  (orderedInterval (-2442200624135549307881560554942053 / 100000000000000000000000000000000000) (-2442200624135500553043915829619653 / 100000000000000000000000000000000000),
   orderedInterval (-875943367454900911919241646999337 / 25000000000000000000000000000000000) (-350377346981955477775188414397717 / 10000000000000000000000000000000000))

theorem besselGridState111_step : besselStateSubset
    (besselIntervalStep (110 * 157 / 50) (157 / 50) 29 besselGridState110) besselGridState111 = true := by
  norm_num [besselGridState110, besselGridState111, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState111_valid : BesselStateValid (111 * 157 / 50 : ℚ) besselGridState111 := by
  have hv := besselIntervalStep_valid (110 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState110 besselGridState110_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (110 * 157 / 50) (157 / 50) 29 besselGridState110)
    (T := besselGridState111) besselGridState111_step hv
  convert hm using 1 <;> norm_num

def besselGridState112 : IntervalRat × IntervalRat :=
  (orderedInterval (2425720752321440978099816848040287 / 100000000000000000000000000000000000) (303215094040186275231515167794507 / 12500000000000000000000000000000000),
   orderedInterval (3491995539018171100391294840638369 / 100000000000000000000000000000000000) (218249721188638777460972890131267 / 6250000000000000000000000000000000))

theorem besselGridState112_step : besselStateSubset
    (besselIntervalStep (111 * 157 / 50) (157 / 50) 29 besselGridState111) besselGridState112 = true := by
  norm_num [besselGridState111, besselGridState112, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState112_valid : BesselStateValid (112 * 157 / 50 : ℚ) besselGridState112 := by
  have hv := besselIntervalStep_valid (111 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState111 besselGridState111_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (111 * 157 / 50) (157 / 50) 29 besselGridState111)
    (T := besselGridState112) besselGridState112_step hv
  convert hm using 1 <;> norm_num

def besselGridState113 : IntervalRat × IntervalRat :=
  (orderedInterval (-2409429203039999772017769370301707 / 100000000000000000000000000000000000) (-1204714601519975039374029040085023 / 50000000000000000000000000000000000),
   orderedInterval (-348038225784890169379944784440547 / 10000000000000000000000000000000000) (-3480382257848851885154493099158139 / 100000000000000000000000000000000000))

theorem besselGridState113_step : besselStateSubset
    (besselIntervalStep (112 * 157 / 50) (157 / 50) 29 besselGridState112) besselGridState113 = true := by
  norm_num [besselGridState112, besselGridState113, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState113_valid : BesselStateValid (113 * 157 / 50 : ℚ) besselGridState113 := by
  have hv := besselIntervalStep_valid (112 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState112 besselGridState112_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (112 * 157 / 50) (157 / 50) 29 besselGridState112)
    (T := besselGridState113) besselGridState113_step hv
  convert hm using 1 <;> norm_num

def besselGridState114 : IntervalRat × IntervalRat :=
  (orderedInterval (478664381725300986937804642688937 / 20000000000000000000000000000000000) (2393321908626555098079717077125789 / 100000000000000000000000000000000000),
   orderedInterval (3468929853125375652039297210521197 / 100000000000000000000000000000000000) (1734464926562712965473643369261229 / 50000000000000000000000000000000000))

theorem besselGridState114_step : besselStateSubset
    (besselIntervalStep (113 * 157 / 50) (157 / 50) 29 besselGridState113) besselGridState114 = true := by
  norm_num [besselGridState113, besselGridState114, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState114_valid : BesselStateValid (114 * 157 / 50 : ℚ) besselGridState114 := by
  have hv := besselIntervalStep_valid (113 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState113 besselGridState113_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (113 * 157 / 50) (157 / 50) 29 besselGridState113)
    (T := besselGridState114) besselGridState114_step hv
  convert hm using 1 <;> norm_num

def besselGridState115 : IntervalRat × IntervalRat :=
  (orderedInterval (-74293591391727552828695378832487 / 3125000000000000000000000000000000) (-2377394924535231056402170051316669 / 100000000000000000000000000000000000),
   orderedInterval (-864408666972138475658695182675729 / 25000000000000000000000000000000000) (-1728817333944251576430273834439111 / 50000000000000000000000000000000000))

theorem besselGridState115_step : besselStateSubset
    (besselIntervalStep (114 * 157 / 50) (157 / 50) 29 besselGridState114) besselGridState115 = true := by
  norm_num [besselGridState114, besselGridState115, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState115_valid : BesselStateValid (115 * 157 / 50 : ℚ) besselGridState115 := by
  have hv := besselIntervalStep_valid (114 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState114 besselGridState114_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (114 * 157 / 50) (157 / 50) 29 besselGridState114)
    (T := besselGridState115) besselGridState115_step hv
  convert hm using 1 <;> norm_num

def besselGridState116 : IntervalRat × IntervalRat :=
  (orderedInterval (2361644424578790335309868346870031 / 100000000000000000000000000000000000) (2361644424578841440756575226227419 / 100000000000000000000000000000000000),
   orderedInterval (3446493156868404922997389091102193 / 100000000000000000000000000000000000) (68929863137369122884838640927249 / 2000000000000000000000000000000000))

theorem besselGridState116_step : besselStateSubset
    (besselIntervalStep (115 * 157 / 50) (157 / 50) 29 besselGridState115) besselGridState116 = true := by
  norm_num [besselGridState115, besselGridState116, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState116_valid : BesselStateValid (116 * 157 / 50 : ℚ) besselGridState116 := by
  have hv := besselIntervalStep_valid (115 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState115 besselGridState115_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (115 * 157 / 50) (157 / 50) 29 besselGridState115)
    (T := besselGridState116) besselGridState116_step hv
  convert hm using 1 <;> norm_num

def besselGridState117 : IntervalRat × IntervalRat :=
  (orderedInterval (-586516674097923208327146665779617 / 25000000000000000000000000000000000) (-469213339278328251185037258946203 / 20000000000000000000000000000000000),
   orderedInterval (-858875470540326017986113520534141 / 25000000000000000000000000000000000) (-1717750941080626189312338466763037 / 50000000000000000000000000000000000))

theorem besselGridState117_step : besselStateSubset
    (besselIntervalStep (116 * 157 / 50) (157 / 50) 29 besselGridState116) besselGridState117 = true := by
  norm_num [besselGridState116, besselGridState117, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState117_valid : BesselStateValid (117 * 157 / 50 : ℚ) besselGridState117 := by
  have hv := besselIntervalStep_valid (116 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState116 besselGridState116_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (116 * 157 / 50) (157 / 50) 29 besselGridState116)
    (T := besselGridState117) besselGridState117_step hv
  convert hm using 1 <;> norm_num

def besselGridState118 : IntervalRat × IntervalRat :=
  (orderedInterval (2330658137104377199956822194154157 / 100000000000000000000000000000000000) (582664534276107312470954482927259 / 25000000000000000000000000000000000),
   orderedInterval (856164377277035643270804956479721 / 25000000000000000000000000000000000) (3424657509108194739084013773618361 / 100000000000000000000000000000000000))

theorem besselGridState118_step : besselStateSubset
    (besselIntervalStep (117 * 157 / 50) (157 / 50) 29 besselGridState117) besselGridState118 = true := by
  norm_num [besselGridState117, besselGridState118, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState118_valid : BesselStateValid (118 * 157 / 50 : ℚ) besselGridState118 := by
  have hv := besselIntervalStep_valid (117 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState117 besselGridState117_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (117 * 157 / 50) (157 / 50) 29 besselGridState117)
    (T := besselGridState118) besselGridState118_step hv
  convert hm using 1 <;> norm_num

def besselGridState119 : IntervalRat × IntervalRat :=
  (orderedInterval (-463083049843535167546984060593531 / 20000000000000000000000000000000000) (-2315415249217623314656592994309067 / 100000000000000000000000000000000000),
   orderedInterval (-853489200591331617051353375051287 / 25000000000000000000000000000000000) (-1706978401182636914458480722021263 / 50000000000000000000000000000000000))

theorem besselGridState119_step : besselStateSubset
    (besselIntervalStep (118 * 157 / 50) (157 / 50) 29 besselGridState118) besselGridState119 = true := by
  norm_num [besselGridState118, besselGridState119, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState119_valid : BesselStateValid (119 * 157 / 50 : ℚ) besselGridState119 := by
  have hv := besselIntervalStep_valid (118 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState118 besselGridState118_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (118 * 157 / 50) (157 / 50) 29 besselGridState118)
    (T := besselGridState119) besselGridState119_step hv
  convert hm using 1 <;> norm_num

def besselGridState120 : IntervalRat × IntervalRat :=
  (orderedInterval (1150167318332346091528424470666267 / 50000000000000000000000000000000000) (2300334636664745179895079471494253 / 100000000000000000000000000000000000),
   orderedInterval (1701698311077491780960283354770163 / 50000000000000000000000000000000000) (3403396622155036675104177315884413 / 100000000000000000000000000000000000))

theorem besselGridState120_step : besselStateSubset
    (besselIntervalStep (119 * 157 / 50) (157 / 50) 29 besselGridState119) besselGridState120 = true := by
  norm_num [besselGridState119, besselGridState120, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState120_valid : BesselStateValid (120 * 157 / 50 : ℚ) besselGridState120 := by
  have hv := besselIntervalStep_valid (119 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState119 besselGridState119_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (119 * 157 / 50) (157 / 50) 29 besselGridState119)
    (T := besselGridState120) besselGridState120_step hv
  convert hm using 1 <;> norm_num

def besselGridState121 : IntervalRat × IntervalRat :=
  (orderedInterval (-571353250263230300876292761229893 / 25000000000000000000000000000000000) (-2285413001052867732297629063825909 / 100000000000000000000000000000000000),
   orderedInterval (-169648696034397923230754891151953 / 5000000000000000000000000000000000) (-212060870042994054807998039635159 / 6250000000000000000000000000000000))

theorem besselGridState121_step : besselStateSubset
    (besselIntervalStep (120 * 157 / 50) (157 / 50) 29 besselGridState120) besselGridState121 = true := by
  norm_num [besselGridState120, besselGridState121, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState121_valid : BesselStateValid (121 * 157 / 50 : ℚ) besselGridState121 := by
  have hv := besselIntervalStep_valid (120 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState120 besselGridState120_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (120 * 157 / 50) (157 / 50) 29 besselGridState120)
    (T := besselGridState121) besselGridState121_step hv
  convert hm using 1 <;> norm_num

def besselGridState122 : IntervalRat × IntervalRat :=
  (orderedInterval (2270647138073809386964640037736459 / 100000000000000000000000000000000000) (1135323569036931666575869706294677 / 50000000000000000000000000000000000),
   orderedInterval (211417858671693671855434002873803 / 6250000000000000000000000000000000) (3382685738747152812486811926993929 / 100000000000000000000000000000000000))

theorem besselGridState122_step : besselStateSubset
    (besselIntervalStep (121 * 157 / 50) (157 / 50) 29 besselGridState121) besselGridState122 = true := by
  norm_num [besselGridState121, besselGridState122, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState122_valid : BesselStateValid (122 * 157 / 50 : ℚ) besselGridState122 := by
  have hv := besselIntervalStep_valid (121 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState121 besselGridState121_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (121 * 157 / 50) (157 / 50) 29 besselGridState121)
    (T := besselGridState122) besselGridState122_step hv
  convert hm using 1 <;> norm_num

def besselGridState123 : IntervalRat × IntervalRat :=
  (orderedInterval (-90241357362968097662766794555919 / 4000000000000000000000000000000000) (-17625265109954281404620533601421 / 781250000000000000000000000000000),
   orderedInterval (-1686264601212815917901412210954211 / 50000000000000000000000000000000000) (-674505840485115459456027429626157 / 20000000000000000000000000000000000))

theorem besselGridState123_step : besselStateSubset
    (besselIntervalStep (122 * 157 / 50) (157 / 50) 29 besselGridState122) besselGridState123 = true := by
  norm_num [besselGridState122, besselGridState123, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState123_valid : BesselStateValid (123 * 157 / 50 : ℚ) besselGridState123 := by
  have hv := besselIntervalStep_valid (122 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState122 besselGridState122_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (122 * 157 / 50) (157 / 50) 29 besselGridState122)
    (T := besselGridState123) besselGridState123_step hv
  convert hm using 1 <;> norm_num

def besselGridState124 : IntervalRat × IntervalRat :=
  (orderedInterval (2241570362777885069551340822317071 / 100000000000000000000000000000000000) (22415703627779399675316493607757 / 1000000000000000000000000000000000),
   orderedInterval (672500304001830793652658628178599 / 20000000000000000000000000000000000) (3362501520009208983119741638887819 / 100000000000000000000000000000000000))

theorem besselGridState124_step : besselStateSubset
    (besselIntervalStep (123 * 157 / 50) (157 / 50) 29 besselGridState123) besselGridState124 = true := by
  norm_num [besselGridState123, besselGridState124, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState124_valid : BesselStateValid (124 * 157 / 50 : ℚ) besselGridState124 := by
  have hv := besselIntervalStep_valid (123 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState123 besselGridState123_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (123 * 157 / 50) (157 / 50) 29 besselGridState123)
    (T := besselGridState124) besselGridState124_step hv
  convert hm using 1 <;> norm_num

def besselGridState125 : IntervalRat × IntervalRat :=
  (orderedInterval (-2227253482152764680486456590000097 / 100000000000000000000000000000000000) (-2227253482152709305690815150108697 / 100000000000000000000000000000000000),
   orderedInterval (-3352599978997096863894141609399293 / 100000000000000000000000000000000000) (-167629998949852068604606418007053 / 5000000000000000000000000000000000))

theorem besselGridState125_step : besselStateSubset
    (besselIntervalStep (124 * 157 / 50) (157 / 50) 29 besselGridState124) besselGridState125 = true := by
  norm_num [besselGridState124, besselGridState125, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState125_valid : BesselStateValid (125 * 157 / 50 : ℚ) besselGridState125 := by
  have hv := besselIntervalStep_valid (124 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState124 besselGridState124_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (124 * 157 / 50) (157 / 50) 29 besselGridState124)
    (T := besselGridState125) besselGridState125_step hv
  convert hm using 1 <;> norm_num

def besselGridState126 : IntervalRat × IntervalRat :=
  (orderedInterval (553270107853203722410587647211419 / 25000000000000000000000000000000000) (553270107853217685466733285790997 / 25000000000000000000000000000000000),
   orderedInterval (52231592863329212360604398033529 / 1562500000000000000000000000000000) (1671410971626562780219462643018591 / 50000000000000000000000000000000000))

theorem besselGridState126_step : besselStateSubset
    (besselIntervalStep (125 * 157 / 50) (157 / 50) 29 besselGridState125) besselGridState126 = true := by
  norm_num [besselGridState125, besselGridState126, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState126_valid : BesselStateValid (126 * 157 / 50 : ℚ) besselGridState126 := by
  have hv := besselIntervalStep_valid (125 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState125 besselGridState125_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (125 * 157 / 50) (157 / 50) 29 besselGridState125)
    (T := besselGridState126) besselGridState126_step hv
  convert hm using 1 <;> norm_num

def besselGridState127 : IntervalRat × IntervalRat :=
  (orderedInterval (-549762107037824620871831140537403 / 25000000000000000000000000000000000) (-2199048428151242153219349241230699 / 100000000000000000000000000000000000),
   orderedInterval (-1666582425140438039360080776006233 / 50000000000000000000000000000000000) (-3333164850280819631188158470059879 / 100000000000000000000000000000000000))

theorem besselGridState127_step : besselStateSubset
    (besselIntervalStep (126 * 157 / 50) (157 / 50) 29 besselGridState126) besselGridState127 = true := by
  norm_num [besselGridState126, besselGridState127, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState127_valid : BesselStateValid (127 * 157 / 50 : ℚ) besselGridState127 := by
  have hv := besselIntervalStep_valid (126 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState126 besselGridState126_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (126 * 157 / 50) (157 / 50) 29 besselGridState126)
    (T := besselGridState127) besselGridState127_step hv
  convert hm using 1 <;> norm_num

def besselGridState128 : IntervalRat × IntervalRat :=
  (orderedInterval (2185154765595171216046981488456599 / 100000000000000000000000000000000000) (1092577382797614012486822911358321 / 50000000000000000000000000000000000),
   orderedInterval (3323626208616360423057252730955323 / 100000000000000000000000000000000000) (3323626208616417349375407320288671 / 100000000000000000000000000000000000))

theorem besselGridState128_step : besselStateSubset
    (besselIntervalStep (127 * 157 / 50) (157 / 50) 29 besselGridState127) besselGridState128 = true := by
  norm_num [besselGridState127, besselGridState128, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState128_valid : BesselStateValid (128 * 157 / 50 : ℚ) besselGridState128 := by
  have hv := besselIntervalStep_valid (127 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState127 besselGridState127_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (127 * 157 / 50) (157 / 50) 29 besselGridState127)
    (T := besselGridState128) besselGridState128_step hv
  convert hm using 1 <;> norm_num

def besselGridState129 : IntervalRat × IntervalRat :=
  (orderedInterval (-2171396809978037626020611274902203 / 100000000000000000000000000000000000) (-434279361995596067563823185472373 / 20000000000000000000000000000000000),
   orderedInterval (-828550898833175739113189884219059 / 25000000000000000000000000000000000) (-132568143813305822029327880715291 / 4000000000000000000000000000000000))

theorem besselGridState129_step : besselStateSubset
    (besselIntervalStep (128 * 157 / 50) (157 / 50) 29 besselGridState128) besselGridState129 = true := by
  norm_num [besselGridState128, besselGridState129, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState129_valid : BesselStateValid (129 * 157 / 50 : ℚ) besselGridState129 := by
  have hv := besselIntervalStep_valid (128 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState128 besselGridState128_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (128 * 157 / 50) (157 / 50) 29 besselGridState128)
    (T := besselGridState129) besselGridState129_step hv
  convert hm using 1 <;> norm_num

def besselGridState130 : IntervalRat × IntervalRat :=
  (orderedInterval (2157771998022237715472655472755443 / 100000000000000000000000000000000000) (2157771998022295483565970748526581 / 100000000000000000000000000000000000),
   orderedInterval (3304894653649969564549333686092939 / 100000000000000000000000000000000000) (826223663412506862571606354368573 / 25000000000000000000000000000000000))

theorem besselGridState130_step : besselStateSubset
    (besselIntervalStep (129 * 157 / 50) (157 / 50) 29 besselGridState129) besselGridState130 = true := by
  norm_num [besselGridState129, besselGridState130, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState130_valid : BesselStateValid (130 * 157 / 50 : ℚ) besselGridState130 := by
  have hv := besselIntervalStep_valid (129 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState129 besselGridState129_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (129 * 157 / 50) (157 / 50) 29 besselGridState129)
    (T := besselGridState130) besselGridState130_step hv
  convert hm using 1 <;> norm_num

def besselGridState131 : IntervalRat × IntervalRat :=
  (orderedInterval (-1072138917264093674552142858728301 / 50000000000000000000000000000000000) (-2144277834528129100501313518559461 / 100000000000000000000000000000000000),
   orderedInterval (-823924272661815860447695056915801 / 25000000000000000000000000000000000) (-3295697090647205075419172445594679 / 100000000000000000000000000000000000))

theorem besselGridState131_step : besselStateSubset
    (besselIntervalStep (130 * 157 / 50) (157 / 50) 29 besselGridState130) besselGridState131 = true := by
  norm_num [besselGridState130, besselGridState131, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState131_valid : BesselStateValid (131 * 157 / 50 : ℚ) besselGridState131 := by
  have hv := besselIntervalStep_valid (130 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState130 besselGridState130_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (130 * 157 / 50) (157 / 50) 29 besselGridState130)
    (T := besselGridState131) besselGridState131_step hv
  convert hm using 1 <;> norm_num

def besselGridState132 : IntervalRat × IntervalRat :=
  (orderedInterval (33295498282220871779595622504551 / 1562500000000000000000000000000000) (53272797251554863090635880128781 / 2500000000000000000000000000000000),
   orderedInterval (328660867506884244050646501329139 / 10000000000000000000000000000000000) (1643304337534450644065220976972843 / 50000000000000000000000000000000000))

theorem besselGridState132_step : besselStateSubset
    (besselIntervalStep (131 * 157 / 50) (157 / 50) 29 besselGridState131) besselGridState132 = true := by
  norm_num [besselGridState131, besselGridState132, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState132_valid : BesselStateValid (132 * 157 / 50 : ℚ) besselGridState132 := by
  have hv := besselIntervalStep_valid (131 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState131 besselGridState131_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (131 * 157 / 50) (157 / 50) 29 besselGridState131)
    (T := besselGridState132) besselGridState132_step hv
  convert hm using 1 <;> norm_num

def besselGridState133 : IntervalRat × IntervalRat :=
  (orderedInterval (-6617724371066028193013386840901 / 312500000000000000000000000000000) (-1058835899370534905142544298240323 / 50000000000000000000000000000000000),
   orderedInterval (-3277627235223194546832114005765401 / 100000000000000000000000000000000000) (-3277627235223135217337047796805987 / 100000000000000000000000000000000000))

theorem besselGridState133_step : besselStateSubset
    (besselIntervalStep (132 * 157 / 50) (157 / 50) 29 besselGridState132) besselGridState133 = true := by
  norm_num [besselGridState132, besselGridState133, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState133_valid : BesselStateValid (133 * 157 / 50 : ℚ) besselGridState133 := by
  have hv := besselIntervalStep_valid (132 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState132 besselGridState132_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (132 * 157 / 50) (157 / 50) 29 besselGridState132)
    (T := besselGridState133) besselGridState133_step hv
  convert hm using 1 <;> norm_num

def besselGridState134 : IntervalRat × IntervalRat :=
  (orderedInterval (1052277628053423351623301956491191 / 50000000000000000000000000000000000) (2104555256106906397094067188035219 / 100000000000000000000000000000000000),
   orderedInterval (817187664241729512818929867476579 / 25000000000000000000000000000000000) (1634375328483488931630731404229733 / 50000000000000000000000000000000000))

theorem besselGridState134_step : besselStateSubset
    (besselIntervalStep (133 * 157 / 50) (157 / 50) 29 besselGridState133) besselGridState134 = true := by
  norm_num [besselGridState133, besselGridState134, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState134_valid : BesselStateValid (134 * 157 / 50 : ℚ) besselGridState134 := by
  have hv := besselIntervalStep_valid (133 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState133 besselGridState133_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (133 * 157 / 50) (157 / 50) 29 besselGridState133)
    (T := besselGridState134) besselGridState134_step hv
  convert hm using 1 <;> norm_num

def besselGridState135 : IntervalRat × IntervalRat :=
  (orderedInterval (-1045780008543846595724362297311073 / 50000000000000000000000000000000000) (-104578000854381650730587610631999 / 5000000000000000000000000000000000),
   orderedInterval (-3259976881772970824922044982401493 / 100000000000000000000000000000000000) (-3259976881772910529825168134758879 / 100000000000000000000000000000000000))

theorem besselGridState135_step : besselStateSubset
    (besselIntervalStep (134 * 157 / 50) (157 / 50) 29 besselGridState134) besselGridState135 = true := by
  norm_num [besselGridState134, besselGridState135, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState135_valid : BesselStateValid (135 * 157 / 50 : ℚ) besselGridState135 := by
  have hv := besselIntervalStep_valid (134 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState134 besselGridState134_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (134 * 157 / 50) (157 / 50) 29 besselGridState134)
    (T := besselGridState135) besselGridState135_step hv
  convert hm using 1 <;> norm_num

def besselGridState136 : IntervalRat × IntervalRat :=
  (orderedInterval (415736778808249151179177823883883 / 20000000000000000000000000000000000) (1039341947020653208172232791169639 / 50000000000000000000000000000000000),
   orderedInterval (25400811756840249601218168608229 / 781250000000000000000000000000000) (1625651952437806363892630809604277 / 50000000000000000000000000000000000))

theorem besselGridState136_step : besselStateSubset
    (besselIntervalStep (135 * 157 / 50) (157 / 50) 29 besselGridState135) besselGridState136 = true := by
  norm_num [besselGridState135, besselGridState136, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState136_valid : BesselStateValid (136 * 157 / 50 : ℚ) besselGridState136 := by
  have hv := besselIntervalStep_valid (135 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState135 besselGridState135_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (135 * 157 / 50) (157 / 50) 29 besselGridState135)
    (T := besselGridState136) besselGridState136_step hv
  convert hm using 1 <;> norm_num

def besselGridState137 : IntervalRat × IntervalRat :=
  (orderedInterval (-2065924754876968005338251218818123 / 100000000000000000000000000000000000) (-516481188719226715163780142217717 / 25000000000000000000000000000000000),
   orderedInterval (-3242729773491690228169994410626823 / 100000000000000000000000000000000000) (-202670610843226810311625212698973 / 6250000000000000000000000000000000))

theorem besselGridState137_step : besselStateSubset
    (besselIntervalStep (136 * 157 / 50) (157 / 50) 29 besselGridState136) besselGridState137 = true := by
  norm_num [besselGridState136, besselGridState137, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState137_valid : BesselStateValid (137 * 157 / 50 : ℚ) besselGridState137 := by
  have hv := besselIntervalStep_valid (136 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState136 besselGridState136_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (136 * 157 / 50) (157 / 50) 29 besselGridState136)
    (T := besselGridState137) besselGridState137_step hv
  convert hm using 1 <;> norm_num

def besselGridState138 : IntervalRat × IntervalRat :=
  (orderedInterval (1026640260625833594868139216105893 / 50000000000000000000000000000000000) (32082508144558262801215151448323 / 1562500000000000000000000000000000),
   orderedInterval (3234252585112161741973974302635489 / 100000000000000000000000000000000000) (129370103404488939605427478962913 / 4000000000000000000000000000000000))

theorem besselGridState138_step : besselStateSubset
    (besselIntervalStep (137 * 157 / 50) (157 / 50) 29 besselGridState137) besselGridState138 = true := by
  norm_num [besselGridState137, besselGridState138, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState138_valid : BesselStateValid (138 * 157 / 50 : ℚ) besselGridState138 := by
  have hv := besselIntervalStep_valid (137 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState137 besselGridState137_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (137 * 157 / 50) (157 / 50) 29 besselGridState137)
    (T := besselGridState138) besselGridState138_step hv
  convert hm using 1 <;> norm_num

def besselGridState139 : IntervalRat × IntervalRat :=
  (orderedInterval (-2040749166838075491049194971226947 / 100000000000000000000000000000000000) (-2040749166838013376024679171215751 / 100000000000000000000000000000000000),
   orderedInterval (-1612935242931133799760066191751353 / 50000000000000000000000000000000000) (-1612935242931102682878379806113711 / 50000000000000000000000000000000000))

theorem besselGridState139_step : besselStateSubset
    (besselIntervalStep (138 * 157 / 50) (157 / 50) 29 besselGridState138) besselGridState139 = true := by
  norm_num [besselGridState138, besselGridState139, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState139_valid : BesselStateValid (139 * 157 / 50 : ℚ) besselGridState139 := by
  have hv := besselIntervalStep_valid (138 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState138 besselGridState138_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (138 * 157 / 50) (157 / 50) 29 besselGridState138)
    (T := besselGridState139) besselGridState139_step hv
  convert hm using 1 <;> norm_num

def besselGridState140 : IntervalRat × IntervalRat :=
  (orderedInterval (2028328715659357439461361599230599 / 100000000000000000000000000000000000) (2028328715659420040594424564034377 / 100000000000000000000000000000000000),
   orderedInterval (3217581668925402829415437164330897 / 100000000000000000000000000000000000) (3217581668925465549405281055760959 / 100000000000000000000000000000000000))

theorem besselGridState140_step : besselStateSubset
    (besselIntervalStep (139 * 157 / 50) (157 / 50) 29 besselGridState139) besselGridState140 = true := by
  norm_num [besselGridState139, besselGridState140, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState140_valid : BesselStateValid (140 * 157 / 50 : ℚ) besselGridState140 := by
  have hv := besselIntervalStep_valid (139 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState139 besselGridState139_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (139 * 157 / 50) (157 / 50) 29 besselGridState139)
    (T := besselGridState140) besselGridState140_step hv
  convert hm using 1 <;> norm_num

def besselGridState141 : IntervalRat × IntervalRat :=
  (orderedInterval (-504004310122586896807762268508827 / 25000000000000000000000000000000000) (-2016017240490284499363056429470199 / 100000000000000000000000000000000000),
   orderedInterval (-802346093257589448121812879335341 / 25000000000000000000000000000000000) (-1604692186515147292822626022390517 / 50000000000000000000000000000000000))

theorem besselGridState141_step : besselStateSubset
    (besselIntervalStep (140 * 157 / 50) (157 / 50) 29 besselGridState140) besselGridState141 = true := by
  norm_num [besselGridState140, besselGridState141, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState141_valid : BesselStateValid (141 * 157 / 50 : ℚ) besselGridState141 := by
  have hv := besselIntervalStep_valid (140 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState140 besselGridState140_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (140 * 157 / 50) (157 / 50) 29 besselGridState140)
    (T := besselGridState141) besselGridState141_step hv
  convert hm using 1 <;> norm_num

def besselGridState142 : IntervalRat × IntervalRat :=
  (orderedInterval (2003812861318598811920109469235621 / 100000000000000000000000000000000000) (250476607664832798393784424288771 / 12500000000000000000000000000000000),
   orderedInterval (80031922024888705892847497661937 / 2500000000000000000000000000000000) (12504987816389109101697709887433 / 390625000000000000000000000000000))

theorem besselGridState142_step : besselStateSubset
    (besselIntervalStep (141 * 157 / 50) (157 / 50) 29 besselGridState141) besselGridState142 = true := by
  norm_num [besselGridState141, besselGridState142, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState142_valid : BesselStateValid (142 * 157 / 50 : ℚ) besselGridState142 := by
  have hv := besselIntervalStep_valid (141 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState141 besselGridState141_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (141 * 157 / 50) (157 / 50) 29 besselGridState141)
    (T := besselGridState142) besselGridState142_step hv
  convert hm using 1 <;> norm_num

def besselGridState143 : IntervalRat × IntervalRat :=
  (orderedInterval (-497928435966606881652842403992537 / 25000000000000000000000000000000000) (-995856871933181731695462262592931 / 50000000000000000000000000000000000),
   orderedInterval (-798314379582871309477412998908389 / 25000000000000000000000000000000000) (-1596628759165710527741394927794213 / 50000000000000000000000000000000000))

theorem besselGridState143_step : besselStateSubset
    (besselIntervalStep (142 * 157 / 50) (157 / 50) 29 besselGridState142) besselGridState143 = true := by
  norm_num [besselGridState142, besselGridState143, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState143_valid : BesselStateValid (143 * 157 / 50 : ℚ) besselGridState143 := by
  have hv := besselIntervalStep_valid (142 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState142 besselGridState142_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (142 * 157 / 50) (157 / 50) 29 besselGridState142)
    (T := besselGridState143) besselGridState143_step hv
  convert hm using 1 <;> norm_num

def besselGridState144 : IntervalRat × IntervalRat :=
  (orderedInterval (989859049083637500164427118289663 / 50000000000000000000000000000000000) (123732381135458722010534241498013 / 6250000000000000000000000000000000),
   orderedInterval (637064930378981674054002797955319 / 20000000000000000000000000000000000) (796331162973743260357833623755421 / 25000000000000000000000000000000000))

theorem besselGridState144_step : besselStateSubset
    (besselIntervalStep (143 * 157 / 50) (157 / 50) 29 besselGridState143) besselGridState144 = true := by
  norm_num [besselGridState143, besselGridState144, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState144_valid : BesselStateValid (144 * 157 / 50 : ℚ) besselGridState144 := by
  have hv := besselIntervalStep_valid (143 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState143 besselGridState143_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (143 * 157 / 50) (157 / 50) 29 besselGridState143)
    (T := besselGridState144) besselGridState144_step hv
  convert hm using 1 <;> norm_num

def besselGridState145 : IntervalRat × IntervalRat :=
  (orderedInterval (-1967824177197916717816142275080599 / 100000000000000000000000000000000000) (-1967824177197851676727366050714733 / 100000000000000000000000000000000000),
   orderedInterval (-3177476688596228021370663020081643 / 100000000000000000000000000000000000) (-3177476688596162860845697106677091 / 100000000000000000000000000000000000))

theorem besselGridState145_step : besselStateSubset
    (besselIntervalStep (144 * 157 / 50) (157 / 50) 29 besselGridState144) besselGridState145 = true := by
  norm_num [besselGridState144, besselGridState145, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState145_valid : BesselStateValid (145 * 157 / 50 : ℚ) besselGridState145 := by
  have hv := besselIntervalStep_valid (144 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState144 besselGridState144_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (144 * 157 / 50) (157 / 50) 29 besselGridState144)
    (T := besselGridState145) besselGridState145_step hv
  convert hm using 1 <;> norm_num

def besselGridState146 : IntervalRat × IntervalRat :=
  (orderedInterval (1956030275560043400684780839479133 / 100000000000000000000000000000000000) (97801513778005446582666980848401 / 5000000000000000000000000000000000),
   orderedInterval (39621400926923678119943253687747 / 1250000000000000000000000000000000) (792428018538489975028534142661473 / 25000000000000000000000000000000000))

theorem besselGridState146_step : besselStateSubset
    (besselIntervalStep (145 * 157 / 50) (157 / 50) 29 besselGridState145) besselGridState146 = true := by
  norm_num [besselGridState145, besselGridState146, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState146_valid : BesselStateValid (146 * 157 / 50 : ℚ) besselGridState146 := by
  have hv := besselIntervalStep_valid (145 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState145 besselGridState145_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (145 * 157 / 50) (157 / 50) 29 besselGridState145)
    (T := besselGridState146) besselGridState146_step hv
  convert hm using 1 <;> norm_num

def besselGridState147 : IntervalRat × IntervalRat :=
  (orderedInterval (-243041841026632426029152236121279 / 12500000000000000000000000000000000) (-1944334728212993386753309497655473 / 100000000000000000000000000000000000),
   orderedInterval (-316202929189764211862824476793791 / 10000000000000000000000000000000000) (-395253661487196997185614291964341 / 12500000000000000000000000000000000))

theorem besselGridState147_step : besselStateSubset
    (besselIntervalStep (146 * 157 / 50) (157 / 50) 29 besselGridState146) besselGridState147 = true := by
  norm_num [besselGridState146, besselGridState147, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState147_valid : BesselStateValid (147 * 157 / 50 : ℚ) besselGridState147 := by
  have hv := besselIntervalStep_valid (146 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState146 besselGridState146_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (146 * 157 / 50) (157 / 50) 29 besselGridState146)
    (T := besselGridState147) besselGridState147_step hv
  convert hm using 1 <;> norm_num

def besselGridState148 : IntervalRat × IntervalRat :=
  (orderedInterval (1932735909251796444569909169764613 / 100000000000000000000000000000000000) (24159198865648286964920031892629 / 1250000000000000000000000000000000),
   orderedInterval (3154426861614395902107563687569417 / 100000000000000000000000000000000000) (394303357701807816813421481393821 / 12500000000000000000000000000000000))

theorem besselGridState148_step : besselStateSubset
    (besselIntervalStep (147 * 157 / 50) (157 / 50) 29 besselGridState147) besselGridState148 = true := by
  norm_num [besselGridState147, besselGridState148, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState148_valid : BesselStateValid (148 * 157 / 50 : ℚ) besselGridState148 := by
  have hv := besselIntervalStep_valid (147 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState147 besselGridState147_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (147 * 157 / 50) (157 / 50) 29 besselGridState147)
    (T := besselGridState148) besselGridState148_step hv
  convert hm using 1 <;> norm_num

def besselGridState149 : IntervalRat × IntervalRat :=
  (orderedInterval (-1921232230731274210260224626795261 / 100000000000000000000000000000000000) (-96061611536560360292972067441361 / 5000000000000000000000000000000000),
   orderedInterval (-3146903338439059279607049766635743 / 100000000000000000000000000000000000) (-3146903338438992155318059565947733 / 100000000000000000000000000000000000))

theorem besselGridState149_step : besselStateSubset
    (besselIntervalStep (148 * 157 / 50) (157 / 50) 29 besselGridState148) besselGridState149 = true := by
  norm_num [besselGridState148, besselGridState149, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState149_valid : BesselStateValid (149 * 157 / 50 : ℚ) besselGridState149 := by
  have hv := besselIntervalStep_valid (148 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState148 besselGridState148_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (148 * 157 / 50) (157 / 50) 29 besselGridState148)
    (T := besselGridState149) besselGridState149_step hv
  convert hm using 1 <;> norm_num

def besselGridState150 : IntervalRat × IntervalRat :=
  (orderedInterval (381964428306470765081663590910833 / 20000000000000000000000000000000000) (1909822141532421322220366780422599 / 100000000000000000000000000000000000),
   orderedInterval (196216081986507093505381649832573 / 6250000000000000000000000000000000) (784864327946045278224466158167331 / 25000000000000000000000000000000000))

theorem besselGridState150_step : besselStateSubset
    (besselIntervalStep (149 * 157 / 50) (157 / 50) 29 besselGridState149) besselGridState150 = true := by
  norm_num [besselGridState149, besselGridState150, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState150_valid : BesselStateValid (150 * 157 / 50 : ℚ) besselGridState150 := by
  have hv := besselIntervalStep_valid (149 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState149 besselGridState149_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (149 * 157 / 50) (157 / 50) 29 besselGridState149)
    (T := besselGridState150) besselGridState150_step hv
  convert hm using 1 <;> norm_num

def besselGridState151 : IntervalRat × IntervalRat :=
  (orderedInterval (-949252063135338581542767893242467 / 50000000000000000000000000000000000) (-237313015783826146653396724632003 / 12500000000000000000000000000000000),
   orderedInterval (-626417480862100852538509841554223 / 20000000000000000000000000000000000) (-3132087404310436152723554277677641 / 100000000000000000000000000000000000))

theorem besselGridState151_step : besselStateSubset
    (besselIntervalStep (150 * 157 / 50) (157 / 50) 29 besselGridState150) besselGridState151 = true := by
  norm_num [besselGridState150, besselGridState151, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState151_valid : BesselStateValid (151 * 157 / 50 : ℚ) besselGridState151 := by
  have hv := besselIntervalStep_valid (150 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState150 besselGridState150_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (150 * 157 / 50) (157 / 50) 29 besselGridState150)
    (T := besselGridState151) besselGridState151_step hv
  convert hm using 1 <;> norm_num

def besselGridState152 : IntervalRat × IntervalRat :=
  (orderedInterval (29488698503794728504361186617629 / 1562500000000000000000000000000000) (1887276704242931107819711897129853 / 100000000000000000000000000000000000),
   orderedInterval (781198067733464153811445111832409 / 25000000000000000000000000000000000) (3124792270933925219007364375134209 / 100000000000000000000000000000000000))

theorem besselGridState152_step : besselStateSubset
    (besselIntervalStep (151 * 157 / 50) (157 / 50) 29 besselGridState151) besselGridState152 = true := by
  norm_num [besselGridState151, besselGridState152, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState152_valid : BesselStateValid (152 * 157 / 50 : ℚ) besselGridState152 := by
  have hv := besselIntervalStep_valid (151 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState151 besselGridState151_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (151 * 157 / 50) (157 / 50) 29 besselGridState151)
    (T := besselGridState152) besselGridState152_step hv
  convert hm using 1 <;> norm_num

def besselGridState153 : IntervalRat × IntervalRat :=
  (orderedInterval (-938069214206295280731406940208023 / 50000000000000000000000000000000000) (-1876138428412521583603188753851791 / 100000000000000000000000000000000000),
   orderedInterval (-194848162366795720900134140446467 / 6250000000000000000000000000000000) (-3117570597868662436211736386088887 / 100000000000000000000000000000000000))

theorem besselGridState153_step : besselStateSubset
    (besselIntervalStep (152 * 157 / 50) (157 / 50) 29 besselGridState152) besselGridState153 = true := by
  norm_num [besselGridState152, besselGridState153, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState153_valid : BesselStateValid (153 * 157 / 50 : ℚ) besselGridState153 := by
  have hv := besselIntervalStep_valid (152 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState152 besselGridState152_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (152 * 157 / 50) (157 / 50) 29 besselGridState152)
    (T := besselGridState153) besselGridState153_step hv
  convert hm using 1 <;> norm_num

def besselGridState154 : IntervalRat × IntervalRat :=
  (orderedInterval (373017576886130634068630015681163 / 20000000000000000000000000000000000) (1865087884430722643159475220463333 / 100000000000000000000000000000000000),
   orderedInterval (1555210550852530563892614747553627 / 50000000000000000000000000000000000) (3110421101705130721041587856294541 / 100000000000000000000000000000000000))

theorem besselGridState154_step : besselStateSubset
    (besselIntervalStep (153 * 157 / 50) (157 / 50) 29 besselGridState153) besselGridState154 = true := by
  norm_num [besselGridState153, besselGridState154, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState154_valid : BesselStateValid (154 * 157 / 50 : ℚ) besselGridState154 := by
  have hv := besselIntervalStep_valid (153 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState153 besselGridState153_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (153 * 157 / 50) (157 / 50) 29 besselGridState153)
    (T := besselGridState154) besselGridState154_step hv
  convert hm using 1 <;> norm_num

def besselGridState155 : IntervalRat × IntervalRat :=
  (orderedInterval (-1854123689691823283312052377304657 / 100000000000000000000000000000000000) (-1854123689691753314900479515599881 / 100000000000000000000000000000000000),
   orderedInterval (-3103342528519691073367721153707857 / 100000000000000000000000000000000000) (-3103342528519620984407405086567079 / 100000000000000000000000000000000000))

theorem besselGridState155_step : besselStateSubset
    (besselIntervalStep (154 * 157 / 50) (157 / 50) 29 besselGridState154) besselGridState155 = true := by
  norm_num [besselGridState154, besselGridState155, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState155_valid : BesselStateValid (155 * 157 / 50 : ℚ) besselGridState155 := by
  have hv := besselIntervalStep_valid (154 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState154 besselGridState154_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (154 * 157 / 50) (157 / 50) 29 besselGridState154)
    (T := besselGridState155) besselGridState155_step hv
  convert hm using 1 <;> norm_num

def besselGridState156 : IntervalRat × IntervalRat :=
  (orderedInterval (921622246211351585197751638320473 / 50000000000000000000000000000000000) (460811123105693408760437413489121 / 25000000000000000000000000000000000),
   orderedInterval (3096333653017247375901260096629253 / 100000000000000000000000000000000000) (154816682650865898060221536532831 / 5000000000000000000000000000000000))

theorem besselGridState156_step : besselStateSubset
    (besselIntervalStep (155 * 157 / 50) (157 / 50) 29 besselGridState155) besselGridState156 = true := by
  norm_num [besselGridState155, besselGridState156, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState156_valid : BesselStateValid (156 * 157 / 50 : ℚ) besselGridState156 := by
  have hv := besselIntervalStep_valid (155 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState155 besselGridState155_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (155 * 157 / 50) (157 / 50) 29 besselGridState155)
    (T := besselGridState156) besselGridState156_step hv
  convert hm using 1 <;> norm_num

def besselGridState157 : IntervalRat × IntervalRat :=
  (orderedInterval (-458112242700903104362839245604457 / 25000000000000000000000000000000000) (-183244897080354145593013196924471 / 10000000000000000000000000000000000),
   orderedInterval (-386174159712931883918663806603997 / 12500000000000000000000000000000000) (-77234831942584599726587492783803 / 2500000000000000000000000000000000))

theorem besselGridState157_step : besselStateSubset
    (besselIntervalStep (156 * 157 / 50) (157 / 50) 29 besselGridState156) besselGridState157 = true := by
  norm_num [besselGridState156, besselGridState157, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState157_valid : BesselStateValid (157 * 157 / 50 : ℚ) besselGridState157 := by
  have hv := besselIntervalStep_valid (156 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState156 besselGridState156_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (156 * 157 / 50) (157 / 50) 29 besselGridState156)
    (T := besselGridState157) besselGridState157_step hv
  convert hm using 1 <;> norm_num

def besselGridState158 : IntervalRat × IntervalRat :=
  (orderedInterval (910867916059373185534852648512937 / 50000000000000000000000000000000000) (1821735832118817830107094625333281 / 100000000000000000000000000000000000),
   orderedInterval (385315029010648859327415505929029 / 12500000000000000000000000000000000) (1541260116042631227264225074603059 / 50000000000000000000000000000000000))

theorem besselGridState158_step : besselStateSubset
    (besselIntervalStep (157 * 157 / 50) (157 / 50) 29 besselGridState157) besselGridState158 = true := by
  norm_num [besselGridState157, besselGridState158, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState158_valid : BesselStateValid (158 * 157 / 50 : ℚ) besselGridState158 := by
  have hv := besselIntervalStep_valid (157 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState157 besselGridState157_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (157 * 157 / 50) (157 / 50) 29 besselGridState157)
    (T := besselGridState158) besselGridState158_step hv
  convert hm using 1 <;> norm_num

def besselGridState159 : IntervalRat × IntervalRat :=
  (orderedInterval (-452775952984463556590762988395981 / 25000000000000000000000000000000000) (-45277595298444556729185770870761 / 2500000000000000000000000000000000),
   orderedInterval (-3075713371900582271715767152087771 / 100000000000000000000000000000000000) (-3075713371900510193541759684352183 / 100000000000000000000000000000000000))

theorem besselGridState159_step : besselStateSubset
    (besselIntervalStep (158 * 157 / 50) (157 / 50) 29 besselGridState158) besselGridState159 = true := by
  norm_num [besselGridState158, besselGridState159, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState159_valid : BesselStateValid (159 * 157 / 50 : ℚ) besselGridState159 := by
  have hv := besselIntervalStep_valid (158 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState158 besselGridState158_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (158 * 157 / 50) (157 / 50) 29 besselGridState158)
    (T := besselGridState159) besselGridState159_step hv
  convert hm using 1 <;> norm_num

def besselGridState160 : IntervalRat × IntervalRat :=
  (orderedInterval (900275836661862278914969710922479 / 50000000000000000000000000000000000) (900275836661898506913371420820869 / 50000000000000000000000000000000000),
   orderedInterval (191810723648342903181903464994631 / 6250000000000000000000000000000000) (1534485789186779513995901040178717 / 50000000000000000000000000000000000))

theorem besselGridState160_step : besselStateSubset
    (besselIntervalStep (159 * 157 / 50) (157 / 50) 29 besselGridState159) besselGridState160 = true := by
  norm_num [besselGridState159, besselGridState160, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState160_valid : BesselStateValid (160 * 157 / 50 : ℚ) besselGridState160 := by
  have hv := besselIntervalStep_valid (159 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState159 besselGridState159_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (159 * 157 / 50) (157 / 50) 29 besselGridState159)
    (T := besselGridState160) besselGridState160_step hv
  convert hm using 1 <;> norm_num

def besselGridState161 : IntervalRat × IntervalRat :=
  (orderedInterval (-179007820606890445614932441006917 / 10000000000000000000000000000000000) (-1790078206068831500707503901863717 / 100000000000000000000000000000000000),
   orderedInterval (-1531146878747917009550073161316327 / 50000000000000000000000000000000000) (-765573439373940235617027461475163 / 25000000000000000000000000000000000))

theorem besselGridState161_step : besselStateSubset
    (besselIntervalStep (160 * 157 / 50) (157 / 50) 29 besselGridState160) besselGridState161 = true := by
  norm_num [besselGridState160, besselGridState161, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState161_valid : BesselStateValid (161 * 157 / 50 : ℚ) besselGridState161 := by
  have hv := besselIntervalStep_valid (160 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState160 besselGridState160_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (160 * 157 / 50) (157 / 50) 29 besselGridState160)
    (T := besselGridState161) besselGridState161_step hv
  convert hm using 1 <;> norm_num

def besselGridState162 : IntervalRat × IntervalRat :=
  (orderedInterval (35593644519119678122738973512159 / 2000000000000000000000000000000000) (222460278244507170208563322507323 / 12500000000000000000000000000000000),
   orderedInterval (15278394196661051462660342045499 / 500000000000000000000000000000000) (1527839419666141934679519652803741 / 50000000000000000000000000000000000))

theorem besselGridState162_step : besselStateSubset
    (besselIntervalStep (161 * 157 / 50) (157 / 50) 29 besselGridState161) besselGridState162 = true := by
  norm_num [besselGridState161, besselGridState162, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState162_valid : BesselStateValid (162 * 157 / 50 : ℚ) besselGridState162 := by
  have hv := besselIntervalStep_valid (161 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState161 besselGridState161_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (161 * 157 / 50) (157 / 50) 29 besselGridState161)
    (T := besselGridState162) besselGridState162_step hv
  convert hm using 1 <;> norm_num

def besselGridState163 : IntervalRat × IntervalRat :=
  (orderedInterval (-442340643511259307468875293059717 / 25000000000000000000000000000000000) (-1769362574044963273608598797323717 / 100000000000000000000000000000000000),
   orderedInterval (-3049125777350320572102428552027887 / 100000000000000000000000000000000000) (-1524562888675123247217691831073647 / 50000000000000000000000000000000000))

theorem besselGridState163_step : besselStateSubset
    (besselIntervalStep (162 * 157 / 50) (157 / 50) 29 besselGridState162) besselGridState163 = true := by
  norm_num [besselGridState162, besselGridState163, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState163_valid : BesselStateValid (163 * 157 / 50 : ℚ) besselGridState163 := by
  have hv := besselIntervalStep_valid (162 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState162 besselGridState162_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (162 * 157 / 50) (157 / 50) 29 besselGridState162)
    (T := besselGridState163) besselGridState163_step hv
  convert hm using 1 <;> norm_num

def besselGridState164 : IntervalRat × IntervalRat :=
  (orderedInterval (1759118115982585986414278237859791 / 100000000000000000000000000000000000) (879559057991330222031510085975553 / 50000000000000000000000000000000000),
   orderedInterval (47541149183933452004511193059143 / 1562500000000000000000000000000000) (3042633547771815507441870879908521 / 100000000000000000000000000000000000))

theorem besselGridState164_step : besselStateSubset
    (besselIntervalStep (163 * 157 / 50) (157 / 50) 29 besselGridState163) besselGridState164 = true := by
  norm_num [besselGridState163, besselGridState164, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState164_valid : BesselStateValid (164 * 157 / 50 : ℚ) besselGridState164 := by
  have hv := besselIntervalStep_valid (163 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState163 besselGridState163_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (163 * 157 / 50) (157 / 50) 29 besselGridState163)
    (T := besselGridState164) besselGridState164_step hv
  convert hm using 1 <;> norm_num

def besselGridState165 : IntervalRat × IntervalRat :=
  (orderedInterval (-69957909653433227825577999247591 / 4000000000000000000000000000000000) (-437236935333938933990371033605363 / 25000000000000000000000000000000000),
   orderedInterval (-759050287236688162312413216939067 / 25000000000000000000000000000000000) (-3036201148946677567963455917294517 / 100000000000000000000000000000000000))

theorem besselGridState165_step : besselStateSubset
    (besselIntervalStep (164 * 157 / 50) (157 / 50) 29 besselGridState164) besselGridState165 = true := by
  norm_num [besselGridState164, besselGridState165, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState165_valid : BesselStateValid (165 * 157 / 50 : ℚ) besselGridState165 := by
  have hv := besselIntervalStep_valid (164 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState164 besselGridState164_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (164 * 157 / 50) (157 / 50) 29 besselGridState164)
    (T := besselGridState165) besselGridState165_step hv
  convert hm using 1 <;> norm_num

def besselGridState166 : IntervalRat × IntervalRat :=
  (orderedInterval (434712590736634669640499241561911 / 25000000000000000000000000000000000) (1738850362946614140917461596457469 / 100000000000000000000000000000000000),
   orderedInterval (3029827600747681133169734414925253 / 100000000000000000000000000000000000) (605965520149551343447360965125913 / 20000000000000000000000000000000000))

theorem besselGridState166_step : besselStateSubset
    (besselIntervalStep (165 * 157 / 50) (157 / 50) 29 besselGridState165) besselGridState166 = true := by
  norm_num [besselGridState165, besselGridState166, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState166_valid : BesselStateValid (166 * 157 / 50 : ℚ) besselGridState166 := by
  have hv := besselIntervalStep_valid (165 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState165 besselGridState165_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (165 * 157 / 50) (157 / 50) 29 besselGridState165)
    (T := besselGridState166) besselGridState166_step hv
  convert hm using 1 <;> norm_num

def besselGridState167 : IntervalRat × IntervalRat :=
  (orderedInterval (-1728824916308481954452199643730033 / 100000000000000000000000000000000000) (-172882491630840598877006958740789 / 10000000000000000000000000000000000),
   orderedInterval (-3023511943984680505812254558199311 / 100000000000000000000000000000000000) (-3023511943984604418315580314481757 / 100000000000000000000000000000000000))

theorem besselGridState167_step : besselStateSubset
    (besselIntervalStep (166 * 157 / 50) (157 / 50) 29 besselGridState166) besselGridState167 = true := by
  norm_num [besselGridState166, besselGridState167, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState167_valid : BesselStateValid (167 * 157 / 50 : ℚ) besselGridState167 := by
  have hv := besselIntervalStep_valid (166 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState166 besselGridState166_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (166 * 157 / 50) (157 / 50) 29 besselGridState166)
    (T := besselGridState167) besselGridState167_step hv
  convert hm using 1 <;> norm_num

def besselGridState168 : IntervalRat × IntervalRat :=
  (orderedInterval (1718870358962826606196704180218267 / 100000000000000000000000000000000000) (429717589740725768963889833507977 / 25000000000000000000000000000000000),
   orderedInterval (754313309959598888659593301437147 / 25000000000000000000000000000000000) (3017253239838472146214282097501051 / 100000000000000000000000000000000000))

theorem besselGridState168_step : besselStateSubset
    (besselIntervalStep (167 * 157 / 50) (157 / 50) 29 besselGridState167) besselGridState168 = true := by
  norm_num [besselGridState167, besselGridState168, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState168_valid : BesselStateValid (168 * 157 / 50 : ℚ) besselGridState168 := by
  have hv := besselIntervalStep_valid (167 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState167 besselGridState167_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (167 * 157 / 50) (157 / 50) 29 besselGridState167)
    (T := besselGridState168) besselGridState168_step hv
  convert hm using 1 <;> norm_num

def besselGridState169 : IntervalRat × IntervalRat :=
  (orderedInterval (-1708985669915506163533388858191347 / 100000000000000000000000000000000000) (-854492834957714594623427323922819 / 50000000000000000000000000000000000),
   orderedInterval (-3011050569313577742066730545511009 / 100000000000000000000000000000000000) (-602210113862700129152210927776541 / 20000000000000000000000000000000000))

theorem besselGridState169_step : besselStateSubset
    (besselIntervalStep (168 * 157 / 50) (157 / 50) 29 besselGridState168) besselGridState169 = true := by
  norm_num [besselGridState168, besselGridState169, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState169_valid : BesselStateValid (169 * 157 / 50 : ℚ) besselGridState169 := by
  have hv := besselIntervalStep_valid (168 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState168 besselGridState168_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (168 * 157 / 50) (157 / 50) 29 besselGridState168)
    (T := besselGridState169) besselGridState169_step hv
  convert hm using 1 <;> norm_num

def besselGridState170 : IntervalRat × IntervalRat :=
  (orderedInterval (1699169849070986696455077475394623 / 100000000000000000000000000000000000) (849584924535532088010570125035209 / 50000000000000000000000000000000000),
   orderedInterval (3004903032708090162411889517944237 / 100000000000000000000000000000000000) (3004903032708167764098767473723447 / 100000000000000000000000000000000000))

theorem besselGridState170_step : besselStateSubset
    (besselIntervalStep (169 * 157 / 50) (157 / 50) 29 besselGridState169) besselGridState170 = true := by
  norm_num [besselGridState169, besselGridState170, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState170_valid : BesselStateValid (170 * 157 / 50 : ℚ) besselGridState170 := by
  have hv := besselIntervalStep_valid (169 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState169 besselGridState169_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (169 * 157 / 50) (157 / 50) 29 besselGridState169)
    (T := besselGridState170) besselGridState170_step hv
  convert hm using 1 <;> norm_num

def besselGridState171 : IntervalRat × IntervalRat :=
  (orderedInterval (-844710958343293849999320830794143 / 50000000000000000000000000000000000) (-1689421916686509714500304002795369 / 100000000000000000000000000000000000),
   orderedInterval (-2998809749101506894009210834013997 / 100000000000000000000000000000000000) (-2998809749101428786288792005845133 / 100000000000000000000000000000000000))

theorem besselGridState171_step : besselStateSubset
    (besselIntervalStep (170 * 157 / 50) (157 / 50) 29 besselGridState170) besselGridState171 = true := by
  norm_num [besselGridState170, besselGridState171, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState171_valid : BesselStateValid (171 * 157 / 50 : ℚ) besselGridState171 := by
  have hv := besselIntervalStep_valid (170 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState170 besselGridState170_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (170 * 157 / 50) (157 / 50) 29 besselGridState170)
    (T := besselGridState171) besselGridState171_step hv
  convert hm using 1 <;> norm_num

def besselGridState172 : IntervalRat × IntervalRat :=
  (orderedInterval (41993522821044143397454999400853 / 2500000000000000000000000000000000) (1679740912841844227982456916080179 / 100000000000000000000000000000000000),
   orderedInterval (748192463964434536691146742239817 / 25000000000000000000000000000000000) (1496384927928908380585895204518809 / 50000000000000000000000000000000000))

theorem besselGridState172_step : besselStateSubset
    (besselIntervalStep (171 * 157 / 50) (157 / 50) 29 besselGridState171) besselGridState172 = true := by
  norm_num [besselGridState171, besselGridState172, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState172_valid : BesselStateValid (172 * 157 / 50 : ℚ) besselGridState172 := by
  have hv := besselIntervalStep_valid (171 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState171 besselGridState171_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (171 * 157 / 50) (157 / 50) 29 besselGridState171)
    (T := besselGridState172) besselGridState172_step hv
  convert hm using 1 <;> norm_num

def besselGridState173 : IntervalRat × IntervalRat :=
  (orderedInterval (-417531474231662536684148089437727 / 25000000000000000000000000000000000) (-835062948463285573705936197242539 / 50000000000000000000000000000000000),
   orderedInterval (-59735650162920186087269185239839 / 2000000000000000000000000000000000) (-597356501629186036523064284243987 / 20000000000000000000000000000000000))

theorem besselGridState173_step : besselStateSubset
    (besselIntervalStep (172 * 157 / 50) (157 / 50) 29 besselGridState172) besselGridState173 = true := by
  norm_num [besselGridState172, besselGridState173, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState173_valid : BesselStateValid (173 * 157 / 50 : ℚ) besselGridState173 := by
  have hv := besselIntervalStep_valid (172 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState172 besselGridState172_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (172 * 157 / 50) (157 / 50) 29 besselGridState172)
    (T := besselGridState173) besselGridState173_step hv
  convert hm using 1 <;> norm_num

def besselGridState174 : IntervalRat × IntervalRat :=
  (orderedInterval (830287973572115402827169493694213 / 50000000000000000000000000000000000) (1660575947144310312874966330268187 / 100000000000000000000000000000000000),
   orderedInterval (2980846878474615764352377119862781 / 100000000000000000000000000000000000) (2980846878474695394096506337908783 / 100000000000000000000000000000000000))

theorem besselGridState174_step : besselStateSubset
    (besselIntervalStep (173 * 157 / 50) (157 / 50) 29 besselGridState173) besselGridState174 = true := by
  norm_num [besselGridState173, besselGridState174, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState174_valid : BesselStateValid (174 * 157 / 50 : ℚ) besselGridState174 := by
  have hv := besselIntervalStep_valid (173 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState173 besselGridState173_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (173 * 157 / 50) (157 / 50) 29 besselGridState173)
    (T := besselGridState174) besselGridState174_step hv
  convert hm using 1 <;> norm_num

def besselGridState175 : IntervalRat × IntervalRat :=
  (orderedInterval (-1651090160030606843223230406799827 / 100000000000000000000000000000000000) (-103193135001907926715646840111139 / 6250000000000000000000000000000000),
   orderedInterval (-23241891845639835506044265733921 / 781250000000000000000000000000000) (-743740539060454701594395027569501 / 25000000000000000000000000000000000))

theorem besselGridState175_step : besselStateSubset
    (besselIntervalStep (174 * 157 / 50) (157 / 50) 29 besselGridState174) besselGridState175 = true := by
  norm_num [besselGridState174, besselGridState175, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState175_valid : BesselStateValid (175 * 157 / 50 : ℚ) besselGridState175 := by
  have hv := besselIntervalStep_valid (174 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState174 besselGridState174_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (174 * 157 / 50) (157 / 50) 29 besselGridState174)
    (T := besselGridState175) besselGridState175_step hv
  convert hm using 1 <;> norm_num

def besselGridState176 : IntervalRat × IntervalRat :=
  (orderedInterval (328333529997536736576727444082853 / 20000000000000000000000000000000000) (820833824993882103933010605024603 / 50000000000000000000000000000000000),
   orderedInterval (2969127547298850452885115806550119 / 100000000000000000000000000000000000) (23196308963272899223359634259639 / 781250000000000000000000000000000))

theorem besselGridState176_step : besselStateSubset
    (besselIntervalStep (175 * 157 / 50) (157 / 50) 29 besselGridState175) besselGridState176 = true := by
  norm_num [besselGridState175, besselGridState176, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState176_valid : BesselStateValid (176 * 157 / 50 : ℚ) besselGridState176 := by
  have hv := besselIntervalStep_valid (175 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState175 besselGridState175_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (175 * 157 / 50) (157 / 50) 29 besselGridState175)
    (T := besselGridState176) besselGridState176_step hv
  convert hm using 1 <;> norm_num

def besselGridState177 : IntervalRat × IntervalRat :=
  (orderedInterval (-1632307548832841952666258417299941 / 100000000000000000000000000000000000) (-816153774416380458908108782364233 / 50000000000000000000000000000000000),
   orderedInterval (-92604446047746945671717046937609 / 3125000000000000000000000000000000) (-185208892095488818988963201457701 / 6250000000000000000000000000000000))

theorem besselGridState177_step : besselStateSubset
    (besselIntervalStep (176 * 157 / 50) (157 / 50) 29 besselGridState176) besselGridState177 = true := by
  norm_num [besselGridState176, besselGridState177, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState177_valid : BesselStateValid (177 * 157 / 50 : ℚ) besselGridState177 := by
  have hv := besselIntervalStep_valid (176 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState176 besselGridState176_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (176 * 157 / 50) (157 / 50) 29 besselGridState176)
    (T := besselGridState177) besselGridState177_step hv
  convert hm using 1 <;> norm_num

def besselGridState178 : IntervalRat × IntervalRat :=
  (orderedInterval (811504502679973957591794312609849 / 50000000000000000000000000000000000) (1623009005360029460560345892903959 / 100000000000000000000000000000000000),
   orderedInterval (92425174138509066249600279900003 / 3125000000000000000000000000000000) (295760557243237178828405735566737 / 10000000000000000000000000000000000))

theorem besselGridState178_step : besselStateSubset
    (besselIntervalStep (177 * 157 / 50) (157 / 50) 29 besselGridState177) besselGridState178 = true := by
  norm_num [besselGridState177, besselGridState178, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState178_valid : BesselStateValid (178 * 157 / 50 : ℚ) besselGridState178 := by
  have hv := besselIntervalStep_valid (177 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState177 besselGridState177_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (177 * 157 / 50) (157 / 50) 29 besselGridState177)
    (T := besselGridState178) besselGridState178_step hv
  convert hm using 1 <;> norm_num

def besselGridState179 : IntervalRat × IntervalRat :=
  (orderedInterval (-161377118491633914844096168274153 / 10000000000000000000000000000000000) (-1613771184916257091877521453825319 / 100000000000000000000000000000000000),
   orderedInterval (-2951916696740656248017129047890011 / 100000000000000000000000000000000000) (-147595834837028703421767817438407 / 5000000000000000000000000000000000))

theorem besselGridState179_step : besselStateSubset
    (besselIntervalStep (178 * 157 / 50) (157 / 50) 29 besselGridState178) besselGridState179 = true := by
  norm_num [besselGridState178, besselGridState179, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState179_valid : BesselStateValid (179 * 157 / 50 : ℚ) besselGridState179 := by
  have hv := besselIntervalStep_valid (178 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState178 besselGridState178_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (178 * 157 / 50) (157 / 50) 29 besselGridState178)
    (T := besselGridState179) besselGridState179_step hv
  convert hm using 1 <;> norm_num

def besselGridState180 : IntervalRat × IntervalRat :=
  (orderedInterval (200574158623766609785466411023961 / 12500000000000000000000000000000000) (401148317247553861673682325143959 / 25000000000000000000000000000000000),
   orderedInterval (1473137457010627198238504892580111 / 50000000000000000000000000000000000) (1473137457010668544002115547038327 / 50000000000000000000000000000000000))

theorem besselGridState180_step : besselStateSubset
    (besselIntervalStep (179 * 157 / 50) (157 / 50) 29 besselGridState179) besselGridState180 = true := by
  norm_num [besselGridState179, besselGridState180, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState180_valid : BesselStateValid (180 * 157 / 50 : ℚ) besselGridState180 := by
  have hv := besselIntervalStep_valid (179 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState179 besselGridState179_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (179 * 157 / 50) (157 / 50) 29 besselGridState179)
    (T := besselGridState180) besselGridState180_step hv
  convert hm using 1 <;> norm_num

def besselGridState181 : IntervalRat × IntervalRat :=
  (orderedInterval (-1595474454812596875873170098635541 / 100000000000000000000000000000000000) (-159547445481251379495282992017687 / 10000000000000000000000000000000000),
   orderedInterval (-2940679506310527710898150272304713 / 100000000000000000000000000000000000) (-294067950631044450676404074014449 / 10000000000000000000000000000000000))

theorem besselGridState181_step : besselStateSubset
    (besselIntervalStep (180 * 157 / 50) (157 / 50) 29 besselGridState180) besselGridState181 = true := by
  norm_num [besselGridState180, besselGridState181, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState181_valid : BesselStateValid (181 * 157 / 50 : ℚ) besselGridState181 := by
  have hv := besselIntervalStep_valid (180 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState180 besselGridState180_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (180 * 157 / 50) (157 / 50) 29 besselGridState180)
    (T := besselGridState181) besselGridState181_step hv
  convert hm using 1 <;> norm_num

def besselGridState182 : IntervalRat × IntervalRat :=
  (orderedInterval (396603488742475994179859949599139 / 25000000000000000000000000000000000) (1586413954969987570811817372236667 / 100000000000000000000000000000000000),
   orderedInterval (2935129769750394396873048789466313 / 100000000000000000000000000000000000) (366891221218809764284550330177607 / 12500000000000000000000000000000000))

theorem besselGridState182_step : besselStateSubset
    (besselIntervalStep (181 * 157 / 50) (157 / 50) 29 besselGridState181) besselGridState182 = true := by
  norm_num [besselGridState181, besselGridState182, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState182_valid : BesselStateValid (182 * 157 / 50 : ℚ) besselGridState182 := by
  have hv := besselIntervalStep_valid (181 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState181 besselGridState181_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (181 * 157 / 50) (157 / 50) 29 besselGridState181)
    (T := besselGridState182) besselGridState182_step hv
  convert hm using 1 <;> norm_num

def besselGridState183 : IntervalRat × IntervalRat :=
  (orderedInterval (-157741099702911275510341244811243 / 10000000000000000000000000000000000) (-788705498514514323587695057240811 / 50000000000000000000000000000000000),
   orderedInterval (-1464812507119556300980928191442243 / 50000000000000000000000000000000000) (-45775390847484818291031006994063 / 1562500000000000000000000000000000))

theorem besselGridState183_step : besselStateSubset
    (besselIntervalStep (182 * 157 / 50) (157 / 50) 29 besselGridState182) besselGridState183 = true := by
  norm_num [besselGridState182, besselGridState183, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState183_valid : BesselStateValid (183 * 157 / 50 : ℚ) besselGridState183 := by
  have hv := besselIntervalStep_valid (182 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState182 besselGridState182_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (182 * 157 / 50) (157 / 50) 29 besselGridState182)
    (T := besselGridState183) besselGridState183_step hv
  convert hm using 1 <;> norm_num

def besselGridState184 : IntervalRat × IntervalRat :=
  (orderedInterval (1568464823172665361320778847632637 / 100000000000000000000000000000000000) (1568464823172749983748966731036607 / 100000000000000000000000000000000000),
   orderedInterval (2924164563090027869097532117190121 / 100000000000000000000000000000000000) (2924164563090112615030114754700267 / 100000000000000000000000000000000000))

theorem besselGridState184_step : besselStateSubset
    (besselIntervalStep (183 * 157 / 50) (157 / 50) 29 besselGridState183) besselGridState184 = true := by
  norm_num [besselGridState183, besselGridState184, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState184_valid : BesselStateValid (184 * 157 / 50 : ℚ) besselGridState184 := by
  have hv := besselIntervalStep_valid (183 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState183 besselGridState183_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (183 * 157 / 50) (157 / 50) 29 besselGridState183)
    (T := besselGridState184) besselGridState184_step hv
  convert hm using 1 <;> norm_num

def besselGridState185 : IntervalRat × IntervalRat :=
  (orderedInterval (-1949468362307930615052322163553 / 125000000000000000000000000000000) (-97473418115391209653004299348317 / 6250000000000000000000000000000000),
   orderedInterval (-1459373876351586254653753582934763 / 50000000000000000000000000000000000) (-583749550540617449622620231757739 / 20000000000000000000000000000000000))

theorem besselGridState185_step : besselStateSubset
    (besselIntervalStep (184 * 157 / 50) (157 / 50) 29 besselGridState184) besselGridState185 = true := by
  norm_num [besselGridState184, besselGridState185, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState185_valid : BesselStateValid (185 * 157 / 50 : ℚ) besselGridState185 := by
  have hv := besselIntervalStep_valid (184 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState184 besselGridState184_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (184 * 157 / 50) (157 / 50) 29 besselGridState184)
    (T := besselGridState185) besselGridState185_step hv
  convert hm using 1 <;> norm_num

def besselGridState186 : IntervalRat × IntervalRat :=
  (orderedInterval (1550739867414947101420251969008837 / 100000000000000000000000000000000000) (310147973483006550969198697788931 / 20000000000000000000000000000000000),
   orderedInterval (2913373932243985385040135993920189 / 100000000000000000000000000000000000) (2913373932244071162162399283694179 / 100000000000000000000000000000000000))

theorem besselGridState186_step : besselStateSubset
    (besselIntervalStep (185 * 157 / 50) (157 / 50) 29 besselGridState185) besselGridState186 = true := by
  norm_num [besselGridState185, besselGridState186, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState186_valid : BesselStateValid (186 * 157 / 50 : ℚ) besselGridState186 := by
  have hv := besselIntervalStep_valid (185 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState185 besselGridState185_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (185 * 157 / 50) (157 / 50) 29 besselGridState185)
    (T := besselGridState186) besselGridState186_step hv
  convert hm using 1 <;> norm_num

def besselGridState187 : IntervalRat × IntervalRat :=
  (orderedInterval (-77097981991535670534690361870713 / 5000000000000000000000000000000000) (-1541959639830627240768844308642763 / 100000000000000000000000000000000000),
   orderedInterval (-2908042463334216661328657553109757 / 100000000000000000000000000000000000) (-2908042463334130367611580619947121 / 100000000000000000000000000000000000))

theorem besselGridState187_step : besselStateSubset
    (besselIntervalStep (186 * 157 / 50) (157 / 50) 29 besselGridState186) besselGridState187 = true := by
  norm_num [besselGridState186, besselGridState187, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState187_valid : BesselStateValid (187 * 157 / 50 : ℚ) besselGridState187 := by
  have hv := besselIntervalStep_valid (186 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState186 besselGridState186_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (186 * 157 / 50) (157 / 50) 29 besselGridState186)
    (T := besselGridState187) besselGridState187_step hv
  convert hm using 1 <;> norm_num

def besselGridState188 : IntervalRat × IntervalRat :=
  (orderedInterval (766616652154366194304045006083113 / 50000000000000000000000000000000000) (12265866434470552605603694304217 / 800000000000000000000000000000000),
   orderedInterval (18142204498432801475809923819253 / 625000000000000000000000000000000) (725688179937333761777339600493417 / 25000000000000000000000000000000000))

theorem besselGridState188_step : besselStateSubset
    (besselIntervalStep (187 * 157 / 50) (157 / 50) 29 besselGridState187) besselGridState188 = true := by
  norm_num [besselGridState187, besselGridState188, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState188_valid : BesselStateValid (188 * 157 / 50 : ℚ) besselGridState188 := by
  have hv := besselIntervalStep_valid (187 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState187 besselGridState187_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (187 * 157 / 50) (157 / 50) 29 besselGridState187)
    (T := besselGridState188) besselGridState188_step hv
  convert hm using 1 <;> norm_num

def besselGridState189 : IntervalRat × IntervalRat :=
  (orderedInterval (-1524560171014456297306856338472587 / 100000000000000000000000000000000000) (-762280085507184546188984184206279 / 50000000000000000000000000000000000),
   orderedInterval (-1448752043563493589697129332509671 / 50000000000000000000000000000000000) (-2897504087126899850482989538102921 / 100000000000000000000000000000000000))

theorem besselGridState189_step : besselStateSubset
    (besselIntervalStep (188 * 157 / 50) (157 / 50) 29 besselGridState188) besselGridState189 = true := by
  norm_num [besselGridState188, besselGridState189, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState189_valid : BesselStateValid (189 * 157 / 50 : ℚ) besselGridState189 := by
  have hv := besselIntervalStep_valid (188 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState188 besselGridState188_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (188 * 157 / 50) (157 / 50) 29 besselGridState188)
    (T := besselGridState189) besselGridState189_step hv
  convert hm using 1 <;> norm_num

def besselGridState190 : IntervalRat × IntervalRat :=
  (orderedInterval (757969781378753143072128537720179 / 50000000000000000000000000000000000) (23686555668087406399682653101399 / 1562500000000000000000000000000000),
   orderedInterval (1446147981341261232980498144418787 / 50000000000000000000000000000000000) (1446147981341305156736747454245727 / 50000000000000000000000000000000000))

theorem besselGridState190_step : besselStateSubset
    (besselIntervalStep (189 * 157 / 50) (157 / 50) 29 besselGridState189) besselGridState190 = true := by
  norm_num [besselGridState189, besselGridState190, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState190_valid : BesselStateValid (190 * 157 / 50 : ℚ) besselGridState190 := by
  have hv := besselIntervalStep_valid (189 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState189 besselGridState189_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (189 * 157 / 50) (157 / 50) 29 besselGridState189)
    (T := besselGridState190) besselGridState190_step hv
  convert hm using 1 <;> norm_num

def besselGridState191 : IntervalRat × IntervalRat :=
  (orderedInterval (-94210675918562086293341654387291 / 6250000000000000000000000000000000) (-376842703674226284520134479703229 / 25000000000000000000000000000000000),
   orderedInterval (-2887127754933792922923587254924513 / 100000000000000000000000000000000000) (-2887127754933704556139200888822469 / 100000000000000000000000000000000000))

theorem besselGridState191_step : besselStateSubset
    (besselIntervalStep (190 * 157 / 50) (157 / 50) 29 besselGridState190) besselGridState191 = true := by
  norm_num [besselGridState190, besselGridState191, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState191_valid : BesselStateValid (191 * 157 / 50 : ℚ) besselGridState191 := by
  have hv := besselIntervalStep_valid (190 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState190 besselGridState190_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (190 * 157 / 50) (157 / 50) 29 besselGridState190)
    (T := besselGridState191) besselGridState191_step hv
  convert hm using 1 <;> norm_num

def besselGridState192 : IntervalRat × IntervalRat :=
  (orderedInterval (374713318513123788912488926668801 / 25000000000000000000000000000000000) (1498853274052583918112254985218413 / 100000000000000000000000000000000000),
   orderedInterval (360249860429051730603683560303197 / 12500000000000000000000000000000000) (2881998883432502731557329368302009 / 100000000000000000000000000000000000))

theorem besselGridState192_step : besselStateSubset
    (besselIntervalStep (191 * 157 / 50) (157 / 50) 29 besselGridState191) besselGridState192 = true := by
  norm_num [besselGridState191, besselGridState192, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState192_valid : BesselStateValid (192 * 157 / 50 : ℚ) besselGridState192 := by
  have hv := besselIntervalStep_valid (191 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState191 besselGridState191_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (191 * 157 / 50) (157 / 50) 29 besselGridState191)
    (T := besselGridState192) besselGridState192_step hv
  convert hm using 1 <;> norm_num

def besselGridState193 : IntervalRat × IntervalRat :=
  (orderedInterval (-93149143739125134070413241724253 / 6250000000000000000000000000000000) (-1490386299825912862142141830609529 / 100000000000000000000000000000000000),
   orderedInterval (-2876908778504998835735597398549909 / 100000000000000000000000000000000000) (-719227194626227357097936368338033 / 25000000000000000000000000000000000))

theorem besselGridState193_step : besselStateSubset
    (besselIntervalStep (192 * 157 / 50) (157 / 50) 29 besselGridState192) besselGridState193 = true := by
  norm_num [besselGridState192, besselGridState193, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState193_valid : BesselStateValid (193 * 157 / 50 : ℚ) besselGridState193 := by
  have hv := besselIntervalStep_valid (192 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState192 besselGridState192_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (192 * 157 / 50) (157 / 50) 29 besselGridState192)
    (T := besselGridState193) besselGridState193_step hv
  convert hm using 1 <;> norm_num

def besselGridState194 : IntervalRat × IntervalRat :=
  (orderedInterval (59278770501157212215091752310727 / 4000000000000000000000000000000000) (740984631264510054778830538963031 / 50000000000000000000000000000000000),
   orderedInterval (114874275239963172374143682973669 / 4000000000000000000000000000000000) (717964220249792309496720633791 / 25000000000000000000000000000000))

theorem besselGridState194_step : besselStateSubset
    (besselIntervalStep (193 * 157 / 50) (157 / 50) 29 besselGridState193) besselGridState194 = true := by
  norm_num [besselGridState193, besselGridState194, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState194_valid : BesselStateValid (194 * 157 / 50 : ℚ) besselGridState194 := by
  have hv := besselIntervalStep_valid (193 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState193 besselGridState193_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (193 * 157 / 50) (157 / 50) 29 besselGridState193)
    (T := besselGridState194) besselGridState194_step hv
  convert hm using 1 <;> norm_num

def besselGridState195 : IntervalRat × IntervalRat :=
  (orderedInterval (-11788812351356811648024138264607 / 800000000000000000000000000000000) (-1473601543919511129952098548464561 / 100000000000000000000000000000000000),
   orderedInterval (-2866842642039045096284926703173481 / 100000000000000000000000000000000000) (-143342132101947732284390899962779 / 5000000000000000000000000000000000))

theorem besselGridState195_step : besselStateSubset
    (besselIntervalStep (194 * 157 / 50) (157 / 50) 29 besselGridState194) besselGridState195 = true := by
  norm_num [besselGridState194, besselGridState195, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState195_valid : BesselStateValid (195 * 157 / 50 : ℚ) besselGridState195 := by
  have hv := besselIntervalStep_valid (194 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState194 besselGridState194_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (194 * 157 / 50) (157 / 50) 29 besselGridState194)
    (T := besselGridState195) besselGridState195_step hv
  convert hm using 1 <;> norm_num

def besselGridState196 : IntervalRat × IntervalRat :=
  (orderedInterval (58611301469809678458093516383391 / 4000000000000000000000000000000000) (732641268372666405024695705779333 / 50000000000000000000000000000000000),
   orderedInterval (2861865522786161569418996682189223 / 100000000000000000000000000000000000) (1430932761393126271327618393038929 / 50000000000000000000000000000000000))

theorem besselGridState196_step : besselStateSubset
    (besselIntervalStep (195 * 157 / 50) (157 / 50) 29 besselGridState195) besselGridState196 = true := by
  norm_num [besselGridState195, besselGridState196, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState196_valid : BesselStateValid (196 * 157 / 50 : ℚ) besselGridState196 := by
  have hv := besselIntervalStep_valid (195 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState195 besselGridState195_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (195 * 157 / 50) (157 / 50) 29 besselGridState195)
    (T := besselGridState196) besselGridState196_step hv
  convert hm using 1 <;> norm_num

def besselGridState197 : IntervalRat × IntervalRat :=
  (orderedInterval (-182126455561748476033258419748287 / 12500000000000000000000000000000000) (-1457011644493896436446365396958237 / 100000000000000000000000000000000000),
   orderedInterval (-571384998841634412198693983632431 / 20000000000000000000000000000000000) (-285692499420808056444185056601373 / 10000000000000000000000000000000000))

theorem besselGridState197_step : besselStateSubset
    (besselIntervalStep (196 * 157 / 50) (157 / 50) 29 besselGridState196) besselGridState197 = true := by
  norm_num [besselGridState196, besselGridState197, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState197_valid : BesselStateValid (197 * 157 / 50 : ℚ) besselGridState197 := by
  have hv := besselIntervalStep_valid (196 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState196 besselGridState196_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (196 * 157 / 50) (157 / 50) 29 besselGridState196)
    (T := besselGridState197) besselGridState197_step hv
  convert hm using 1 <;> norm_num

def besselGridState198 : IntervalRat × IntervalRat :=
  (orderedInterval (289757656230179677299148032545681 / 20000000000000000000000000000000000) (1448788281150990282215535982473353 / 100000000000000000000000000000000000),
   orderedInterval (356502567106561517050040734834053 / 12500000000000000000000000000000000) (2852020536852584156944508264519053 / 100000000000000000000000000000000000))

theorem besselGridState198_step : besselStateSubset
    (besselIntervalStep (197 * 157 / 50) (157 / 50) 29 besselGridState197) besselGridState198 = true := by
  norm_num [besselGridState197, besselGridState198, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState198_valid : BesselStateValid (198 * 157 / 50 : ℚ) besselGridState198 := by
  have hv := besselIntervalStep_valid (197 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState197 besselGridState197_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (197 * 157 / 50) (157 / 50) 29 besselGridState197)
    (T := besselGridState198) besselGridState198_step hv
  convert hm using 1 <;> norm_num

def besselGridState199 : IntervalRat × IntervalRat :=
  (orderedInterval (-36015296774088797194366950093361 / 2500000000000000000000000000000000) (-720305935481729733738204948204753 / 50000000000000000000000000000000000),
   orderedInterval (-711787910157147105305632141851911 / 25000000000000000000000000000000000) (-2847151640628495876007662175861041 / 100000000000000000000000000000000000))

theorem besselGridState199_step : besselStateSubset
    (besselIntervalStep (198 * 157 / 50) (157 / 50) 29 besselGridState198) besselGridState199 = true := by
  norm_num [besselGridState198, besselGridState199, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState199_valid : BesselStateValid (199 * 157 / 50 : ℚ) besselGridState199 := by
  have hv := besselIntervalStep_valid (198 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState198 besselGridState198_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (198 * 157 / 50) (157 / 50) 29 besselGridState198)
    (T := besselGridState199) besselGridState199_step hv
  convert hm using 1 <;> norm_num

def besselGridState200 : IntervalRat × IntervalRat :=
  (orderedInterval (1432481848211174935769652526095093 / 100000000000000000000000000000000000) (8953011551320424258285660639579 / 625000000000000000000000000000000),
   orderedInterval (2842317804593498029107670138863267 / 100000000000000000000000000000000000) (2842317804593591099672279947722319 / 100000000000000000000000000000000000))

theorem besselGridState200_step : besselStateSubset
    (besselIntervalStep (199 * 157 / 50) (157 / 50) 29 besselGridState199) besselGridState200 = true := by
  norm_num [besselGridState199, besselGridState200, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState200_valid : BesselStateValid (200 * 157 / 50 : ℚ) besselGridState200 := by
  have hv := besselIntervalStep_valid (199 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState199 besselGridState199_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (199 * 157 / 50) (157 / 50) 29 besselGridState199)
    (T := besselGridState200) besselGridState200_step hv
  convert hm using 1 <;> norm_num

def besselGridState201 : IntervalRat × IntervalRat :=
  (orderedInterval (-284879531396592559890916388164797 / 20000000000000000000000000000000000) (-356099414245717331990123809140787 / 25000000000000000000000000000000000),
   orderedInterval (-1418759268373081977785130714668263 / 50000000000000000000000000000000000) (-283751853674607035897590909530483 / 10000000000000000000000000000000000))

theorem besselGridState201_step : besselStateSubset
    (besselIntervalStep (200 * 157 / 50) (157 / 50) 29 besselGridState200) besselGridState201 = true := by
  norm_num [besselGridState200, besselGridState201, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState201_valid : BesselStateValid (201 * 157 / 50 : ℚ) besselGridState201 := by
  have hv := besselIntervalStep_valid (200 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState200 besselGridState200_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (200 * 157 / 50) (157 / 50) 29 besselGridState200)
    (T := besselGridState201) besselGridState201_step hv
  convert hm using 1 <;> norm_num

def besselGridState202 : IntervalRat × IntervalRat :=
  (orderedInterval (1416358750959491517261967581892619 / 100000000000000000000000000000000000) (708179375479792757687636639206477 / 50000000000000000000000000000000000),
   orderedInterval (2832753353824490434847208372829947 / 100000000000000000000000000000000000) (2832753353824584558152243296326699 / 100000000000000000000000000000000000))

theorem besselGridState202_step : besselStateSubset
    (besselIntervalStep (201 * 157 / 50) (157 / 50) 29 besselGridState201) besselGridState202 = true := by
  norm_num [besselGridState201, besselGridState202, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState202_valid : BesselStateValid (202 * 157 / 50 : ℚ) besselGridState202 := by
  have hv := besselIntervalStep_valid (201 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState201 besselGridState201_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (201 * 157 / 50) (157 / 50) 29 besselGridState201)
    (T := besselGridState202) besselGridState202_step hv
  convert hm using 1 <;> norm_num

def besselGridState203 : IntervalRat × IntervalRat :=
  (orderedInterval (-70418229660148026960382737637757 / 5000000000000000000000000000000000) (-1408364593202866013793006265227439 / 100000000000000000000000000000000000),
   orderedInterval (-353502722638859396413969464700281 / 12500000000000000000000000000000000) (-707005445277695130153538980056147 / 25000000000000000000000000000000000))

theorem besselGridState203_step : besselStateSubset
    (besselIntervalStep (202 * 157 / 50) (157 / 50) 29 besselGridState202) besselGridState203 = true := by
  norm_num [besselGridState202, besselGridState203, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState203_valid : BesselStateValid (203 * 157 / 50 : ℚ) besselGridState203 := by
  have hv := besselIntervalStep_valid (202 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState202 besselGridState202_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (202 * 157 / 50) (157 / 50) 29 besselGridState202)
    (T := besselGridState203) besselGridState203_step hv
  convert hm using 1 <;> norm_num

def besselGridState204 : IntervalRat × IntervalRat :=
  (orderedInterval (1400414655950114462088677193300013 / 100000000000000000000000000000000000) (700207327975104757743865968259601 / 50000000000000000000000000000000000),
   orderedInterval (2823323352240068983468212787646069 / 100000000000000000000000000000000000) (112932934089606566489648129224101 / 4000000000000000000000000000000000))

theorem besselGridState204_step : besselStateSubset
    (besselIntervalStep (203 * 157 / 50) (157 / 50) 29 besselGridState203) besselGridState204 = true := by
  norm_num [besselGridState203, besselGridState204, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState204_valid : BesselStateValid (204 * 157 / 50 : ℚ) besselGridState204 := by
  have hv := besselIntervalStep_valid (203 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState203 besselGridState203_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (203 * 157 / 50) (157 / 50) 29 besselGridState203)
    (T := besselGridState204) besselGridState204_step hv
  convert hm using 1 <;> norm_num

def besselGridState205 : IntervalRat × IntervalRat :=
  (orderedInterval (-696254210206831832062586064047889 / 50000000000000000000000000000000000) (-1392508420413568082057706665101757 / 100000000000000000000000000000000000),
   orderedInterval (-352332201126900039392854008735919 / 12500000000000000000000000000000000) (-2818657609015104607610680451784229 / 100000000000000000000000000000000000))

theorem besselGridState205_step : besselStateSubset
    (besselIntervalStep (204 * 157 / 50) (157 / 50) 29 besselGridState204) besselGridState205 = true := by
  norm_num [besselGridState204, besselGridState205, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState205_valid : BesselStateValid (205 * 157 / 50 : ℚ) besselGridState205 := by
  have hv := besselIntervalStep_valid (204 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState204 besselGridState204_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (204 * 157 / 50) (157 / 50) 29 besselGridState204)
    (T := besselGridState205) besselGridState205_step hv
  convert hm using 1 <;> norm_num

def besselGridState206 : IntervalRat × IntervalRat :=
  (orderedInterval (692322688292999156271309921161087 / 50000000000000000000000000000000000) (1384645376586094423963442824074951 / 100000000000000000000000000000000000),
   orderedInterval (1407012050612880198003537522540033 / 50000000000000000000000000000000000) (281402410122585663298310439974827 / 10000000000000000000000000000000000))

theorem besselGridState206_step : besselStateSubset
    (besselIntervalStep (205 * 157 / 50) (157 / 50) 29 besselGridState205) besselGridState206 = true := by
  norm_num [besselGridState205, besselGridState206, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState206_valid : BesselStateValid (206 * 157 / 50 : ℚ) besselGridState206 := by
  have hv := besselIntervalStep_valid (205 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState205 besselGridState205_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (205 * 157 / 50) (157 / 50) 29 besselGridState205)
    (T := besselGridState206) besselGridState206_step hv
  convert hm using 1 <;> norm_num

def besselGridState207 : IntervalRat × IntervalRat :=
  (orderedInterval (-1376825023051095803975350016560011 / 100000000000000000000000000000000000) (-1376825023050999162515279044624117 / 100000000000000000000000000000000000),
   orderedInterval (-1404711193236733076452347791282823 / 50000000000000000000000000000000000) (-2809422386473369385799124620725717 / 100000000000000000000000000000000000))

theorem besselGridState207_step : besselStateSubset
    (besselIntervalStep (206 * 157 / 50) (157 / 50) 29 besselGridState206) besselGridState207 = true := by
  norm_num [besselGridState206, besselGridState207, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState207_valid : BesselStateValid (207 * 157 / 50 : ℚ) besselGridState207 := by
  have hv := besselIntervalStep_valid (206 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState206 besselGridState206_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (206 * 157 / 50) (157 / 50) 29 besselGridState206)
    (T := besselGridState207) besselGridState207_step hv
  convert hm using 1 <;> norm_num

def besselGridState208 : IntervalRat × IntervalRat :=
  (orderedInterval (1369046866798360765941085512422013 / 100000000000000000000000000000000000) (1369046866798457938127239957984389 / 100000000000000000000000000000000000),
   orderedInterval (140242601499987035105249899008363 / 5000000000000000000000000000000000) (2804852029999838000026723009634313 / 100000000000000000000000000000000000))

theorem besselGridState208_step : besselStateSubset
    (besselIntervalStep (207 * 157 / 50) (157 / 50) 29 besselGridState207) besselGridState208 = true := by
  norm_num [besselGridState207, besselGridState208, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState208_valid : BesselStateValid (208 * 157 / 50 : ℚ) besselGridState208 := by
  have hv := besselIntervalStep_valid (207 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState207 besselGridState207_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (207 * 157 / 50) (157 / 50) 29 besselGridState207)
    (T := besselGridState208) besselGridState208_step hv
  convert hm using 1 <;> norm_num

def besselGridState209 : IntervalRat × IntervalRat :=
  (orderedInterval (-340327605761094271910638621514191 / 25000000000000000000000000000000000) (-680655211522139692021267364893981 / 50000000000000000000000000000000000),
   orderedInterval (-70007815113020184276235910917369 / 2500000000000000000000000000000000) (-280031260452070954162399500534621 / 10000000000000000000000000000000000))

theorem besselGridState209_step : besselStateSubset
    (besselIntervalStep (208 * 157 / 50) (157 / 50) 29 besselGridState208) besselGridState209 = true := by
  norm_num [besselGridState208, besselGridState209, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState209_valid : BesselStateValid (209 * 157 / 50 : ℚ) besselGridState209 := by
  have hv := besselIntervalStep_valid (208 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState208 besselGridState208_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (208 * 157 / 50) (157 / 50) 29 besselGridState208)
    (T := besselGridState209) besselGridState209_step hv
  convert hm using 1 <;> norm_num

def besselGridState210 : IntervalRat × IntervalRat :=
  (orderedInterval (270723043011250922816571249941877 / 20000000000000000000000000000000000) (270723043011270569957094170211621 / 20000000000000000000000000000000000),
   orderedInterval (559160738012816004450924419217467 / 20000000000000000000000000000000000) (349475461258022297984036678072329 / 12500000000000000000000000000000000))

theorem besselGridState210_step : besselStateSubset
    (besselIntervalStep (209 * 157 / 50) (157 / 50) 29 besselGridState209) besselGridState210 = true := by
  norm_num [besselGridState209, besselGridState210, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState210_valid : BesselStateValid (210 * 157 / 50 : ℚ) besselGridState210 := by
  have hv := besselIntervalStep_valid (209 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState209 besselGridState209_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (209 * 157 / 50) (157 / 50) 29 besselGridState209)
    (T := besselGridState210) besselGridState210_step hv
  convert hm using 1 <;> norm_num

def besselGridState211 : IntervalRat × IntervalRat :=
  (orderedInterval (-1345960773982628625816858451539791 / 100000000000000000000000000000000000) (-672980386991264928660985213873641 / 50000000000000000000000000000000000),
   orderedInterval (-5451806394163913598333253754119 / 195312500000000000000000000000000) (-2791324873811824867847258749772123 / 100000000000000000000000000000000000))

theorem besselGridState211_step : besselStateSubset
    (besselIntervalStep (210 * 157 / 50) (157 / 50) 29 besselGridState210) besselGridState211 = true := by
  norm_num [besselGridState210, besselGridState211, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState211_valid : BesselStateValid (211 * 157 / 50 : ℚ) besselGridState211 := by
  have hv := besselIntervalStep_valid (210 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState210 besselGridState210_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (210 * 157 / 50) (157 / 50) 29 besselGridState210)
    (T := besselGridState211) besselGridState211_step hv
  convert hm using 1 <;> norm_num

def besselGridState212 : IntervalRat × IntervalRat :=
  (orderedInterval (53533865547437487216065576118801 / 4000000000000000000000000000000000) (53533865547441459295177192691913 / 4000000000000000000000000000000000),
   orderedInterval (2786875749946410727760220720982629 / 100000000000000000000000000000000000) (2786875749946510155831703428940671 / 100000000000000000000000000000000000))

theorem besselGridState212_step : besselStateSubset
    (besselIntervalStep (211 * 157 / 50) (157 / 50) 29 besselGridState211) besselGridState212 = true := by
  norm_num [besselGridState211, besselGridState212, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState212_valid : BesselStateValid (212 * 157 / 50 : ℚ) besselGridState212 := by
  have hv := besselIntervalStep_valid (211 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState211 besselGridState211_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (211 * 157 / 50) (157 / 50) 29 besselGridState211)
    (T := besselGridState212) besselGridState212_step hv
  convert hm using 1 <;> norm_num

def besselGridState213 : IntervalRat × IntervalRat :=
  (orderedInterval (-166346544447764052461147621067033 / 12500000000000000000000000000000000) (-66538617779100629176845372753787 / 5000000000000000000000000000000000),
   orderedInterval (-695613979875305632612928963829089 / 25000000000000000000000000000000000) (-2782455919501122568116742878088999 / 100000000000000000000000000000000000))

theorem besselGridState213_step : besselStateSubset
    (besselIntervalStep (212 * 157 / 50) (157 / 50) 29 besselGridState212) besselGridState213 = true := by
  norm_num [besselGridState212, besselGridState213, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState213_valid : BesselStateValid (213 * 157 / 50 : ℚ) besselGridState213 := by
  have hv := besselIntervalStep_valid (212 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState212 besselGridState212_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (212 * 157 / 50) (157 / 50) 29 besselGridState212)
    (T := besselGridState213) besselGridState213_step hv
  convert hm using 1 <;> norm_num

def besselGridState214 : IntervalRat × IntervalRat :=
  (orderedInterval (1323237478481252374506172477190727 / 100000000000000000000000000000000000) (6616187392406763727627314453537 / 500000000000000000000000000000000),
   orderedInterval (694516247553566256042851449048401 / 25000000000000000000000000000000000) (347258123776795690182775014768757 / 12500000000000000000000000000000000))

theorem besselGridState214_step : besselStateSubset
    (besselIntervalStep (213 * 157 / 50) (157 / 50) 29 besselGridState213) besselGridState214 = true := by
  norm_num [besselGridState213, besselGridState214, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState214_valid : BesselStateValid (214 * 157 / 50 : ℚ) besselGridState214 := by
  have hv := besselIntervalStep_valid (213 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState213 besselGridState213_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (213 * 157 / 50) (157 / 50) 29 besselGridState213)
    (T := besselGridState214) besselGridState214_step hv
  convert hm using 1 <;> norm_num

def besselGridState215 : IntervalRat × IntervalRat :=
  (orderedInterval (-1315741568435486754663536353630921 / 100000000000000000000000000000000000) (-657870784217692924041870396473041 / 50000000000000000000000000000000000),
   orderedInterval (-2773702576387223912108065598078281 / 100000000000000000000000000000000000) (-1386851288193561439584080605534461 / 50000000000000000000000000000000000))

theorem besselGridState215_step : besselStateSubset
    (besselIntervalStep (214 * 157 / 50) (157 / 50) 29 besselGridState214) besselGridState215 = true := by
  norm_num [besselGridState214, besselGridState215, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState215_valid : BesselStateValid (215 * 157 / 50 : ℚ) besselGridState215 := by
  have hv := besselIntervalStep_valid (214 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState214 besselGridState214_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (214 * 157 / 50) (157 / 50) 29 besselGridState214)
    (T := besselGridState215) besselGridState215_step hv
  convert hm using 1 <;> norm_num

def besselGridState216 : IntervalRat × IntervalRat :=
  (orderedInterval (654142096793771897186413262117587 / 50000000000000000000000000000000000) (1308284193587645237207571281294783 / 100000000000000000000000000000000000),
   orderedInterval (2769368298745566942290339784836113 / 100000000000000000000000000000000000) (2769368298745668511573601908225417 / 100000000000000000000000000000000000))

theorem besselGridState216_step : besselStateSubset
    (besselIntervalStep (215 * 157 / 50) (157 / 50) 29 besselGridState215) besselGridState216 = true := by
  norm_num [besselGridState215, besselGridState216, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState216_valid : BesselStateValid (216 * 157 / 50 : ℚ) besselGridState216 := by
  have hv := besselIntervalStep_valid (215 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState215 besselGridState215_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (215 * 157 / 50) (157 / 50) 29 besselGridState215)
    (T := besselGridState216) besselGridState216_step hv
  convert hm using 1 <;> norm_num

def besselGridState217 : IntervalRat × IntervalRat :=
  (orderedInterval (-1300864929026308493992170984137139 / 100000000000000000000000000000000000) (-325216232256551628551768955362813 / 25000000000000000000000000000000000),
   orderedInterval (-43204090379770275788943895010551 / 1562500000000000000000000000000000) (-1382530892152597772085290744687463 / 50000000000000000000000000000000000))

theorem besselGridState217_step : besselStateSubset
    (besselIntervalStep (216 * 157 / 50) (157 / 50) 29 besselGridState216) besselGridState217 = true := by
  norm_num [besselGridState216, besselGridState217, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState217_valid : BesselStateValid (217 * 157 / 50 : ℚ) besselGridState217 := by
  have hv := besselIntervalStep_valid (216 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState216 besselGridState216_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (216 * 157 / 50) (157 / 50) 29 besselGridState216)
    (T := besselGridState217) besselGridState217_step hv
  convert hm using 1 <;> norm_num

def besselGridState218 : IntervalRat × IntervalRat :=
  (orderedInterval (1293483356642819012756031820570199 / 100000000000000000000000000000000000) (258696671328584306037567423634879 / 20000000000000000000000000000000000),
   orderedInterval (2760782666239905659992939925061023 / 100000000000000000000000000000000000) (2760782666240008304049502888245591 / 100000000000000000000000000000000000))

theorem besselGridState218_step : besselStateSubset
    (besselIntervalStep (217 * 157 / 50) (157 / 50) 29 besselGridState217) besselGridState218 = true := by
  norm_num [besselGridState217, besselGridState218, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState218_valid : BesselStateValid (218 * 157 / 50 : ℚ) besselGridState218 := by
  have hv := besselIntervalStep_valid (217 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState217 besselGridState217_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (217 * 157 / 50) (157 / 50) 29 besselGridState217)
    (T := besselGridState218) besselGridState218_step hv
  convert hm using 1 <;> norm_num

def besselGridState219 : IntervalRat × IntervalRat :=
  (orderedInterval (-160767383124133492059859964105867 / 12500000000000000000000000000000000) (-1286139064992964880703044668949889 / 100000000000000000000000000000000000),
   orderedInterval (-1378265291876947248338909335566861 / 50000000000000000000000000000000000) (-2756530583753791314189388144397911 / 100000000000000000000000000000000000))

theorem besselGridState219_step : besselStateSubset
    (besselIntervalStep (218 * 157 / 50) (157 / 50) 29 besselGridState218) besselGridState219 = true := by
  norm_num [besselGridState218, besselGridState219, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState219_valid : BesselStateValid (219 * 157 / 50 : ℚ) besselGridState219 := by
  have hv := besselIntervalStep_valid (218 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState218 besselGridState218_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (218 * 157 / 50) (157 / 50) 29 besselGridState218)
    (T := besselGridState219) besselGridState219_step hv
  convert hm using 1 <;> norm_num

def besselGridState220 : IntervalRat × IntervalRat :=
  (orderedInterval (4995436129535133056786190765079 / 390625000000000000000000000000000) (639415824580548828677705241798317 / 50000000000000000000000000000000000),
   orderedInterval (2752305181956270423496713659806383 / 100000000000000000000000000000000000) (275230518195637414511510834769683 / 10000000000000000000000000000000000))

theorem besselGridState220_step : besselStateSubset
    (besselIntervalStep (219 * 157 / 50) (157 / 50) 29 besselGridState219) besselGridState220 = true := by
  norm_num [besselGridState219, besselGridState220, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState220_valid : BesselStateValid (220 * 157 / 50 : ℚ) besselGridState220 := by
  have hv := besselIntervalStep_valid (219 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState219 besselGridState219_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (219 * 157 / 50) (157 / 50) 29 besselGridState219)
    (T := besselGridState220) besselGridState220_step hv
  convert hm using 1 <;> norm_num

def besselGridState221 : IntervalRat × IntervalRat :=
  (orderedInterval (-1271560710628107394531669349217593 / 100000000000000000000000000000000000) (-1271560710628003259971969627785219 / 100000000000000000000000000000000000),
   orderedInterval (-1374053055870224432114399908421273 / 50000000000000000000000000000000000) (-2748106111740344602781378843046321 / 100000000000000000000000000000000000))

theorem besselGridState221_step : besselStateSubset
    (besselIntervalStep (220 * 157 / 50) (157 / 50) 29 besselGridState220) besselGridState221 = true := by
  norm_num [besselGridState220, besselGridState221, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState221_valid : BesselStateValid (221 * 157 / 50 : ℚ) besselGridState221 := by
  have hv := besselIntervalStep_valid (220 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState220 besselGridState220_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (220 * 157 / 50) (157 / 50) 29 besselGridState220)
    (T := besselGridState221) besselGridState221_step hv
  convert hm using 1 <;> norm_num

def besselGridState222 : IntervalRat × IntervalRat :=
  (orderedInterval (158040732142883891415817525493517 / 12500000000000000000000000000000000) (9877545758931060986937511323681 / 781250000000000000000000000000000),
   orderedInterval (274393302966389969635508621898501 / 10000000000000000000000000000000000) (1371966514832002249165781227372389 / 50000000000000000000000000000000000))

theorem besselGridState222_step : besselStateSubset
    (besselIntervalStep (221 * 157 / 50) (157 / 50) 29 besselGridState221) besselGridState222 = true := by
  norm_num [besselGridState221, besselGridState222, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState222_valid : BesselStateValid (222 * 157 / 50 : ℚ) besselGridState222 := by
  have hv := besselIntervalStep_valid (221 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState221 besselGridState221_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (221 * 157 / 50) (157 / 50) 29 besselGridState221)
    (T := besselGridState222) besselGridState222_step hv
  convert hm using 1 <;> norm_num

def besselGridState223 : IntervalRat × IntervalRat :=
  (orderedInterval (-314281675649439736701333602186769 / 25000000000000000000000000000000000) (-1257126702597653730660938838121407 / 100000000000000000000000000000000000),
   orderedInterval (-1369892798917031627610696704807159 / 50000000000000000000000000000000000) (-2739785597833957912014864757440843 / 100000000000000000000000000000000000))

theorem besselGridState223_step : besselStateSubset
    (besselIntervalStep (222 * 157 / 50) (157 / 50) 29 besselGridState222) besselGridState223 = true := by
  norm_num [besselGridState222, besselGridState223, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState223_valid : BesselStateValid (223 * 157 / 50 : ℚ) besselGridState223 := by
  have hv := besselIntervalStep_valid (222 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState222 besselGridState222_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (222 * 157 / 50) (157 / 50) 29 besselGridState222)
    (T := besselGridState223) besselGridState223_step hv
  convert hm using 1 <;> norm_num

def besselGridState224 : IntervalRat × IntervalRat :=
  (orderedInterval (624981433451524394515598460334033 / 50000000000000000000000000000000000) (312490716725788636755166585139337 / 25000000000000000000000000000000000),
   orderedInterval (547132696758759086202294457217679 / 20000000000000000000000000000000000) (27356634837939013161500200175109 / 1000000000000000000000000000000000))

theorem besselGridState224_step : besselStateSubset
    (besselIntervalStep (223 * 157 / 50) (157 / 50) 29 besselGridState223) besselGridState224 = true := by
  norm_num [besselGridState223, besselGridState224, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState224_valid : BesselStateValid (224 * 157 / 50 : ℚ) besselGridState224 := by
  have hv := besselIntervalStep_valid (223 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState223 besselGridState223_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (223 * 157 / 50) (157 / 50) 29 besselGridState223)
    (T := besselGridState224) besselGridState224_step hv
  convert hm using 1 <;> norm_num

def besselGridState225 : IntervalRat × IntervalRat :=
  (orderedInterval (-621416987935473390112495676736399 / 50000000000000000000000000000000000) (-310708493967710119921835115706071 / 25000000000000000000000000000000000),
   orderedInterval (-2731566360412948677369210926953689 / 100000000000000000000000000000000000) (-2731566360412842249595706612181177 / 100000000000000000000000000000000000))

theorem besselGridState225_step : besselStateSubset
    (besselIntervalStep (224 * 157 / 50) (157 / 50) 29 besselGridState224) besselGridState225 = true := by
  norm_num [besselGridState224, besselGridState225, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState225_valid : BesselStateValid (225 * 157 / 50 : ℚ) besselGridState225 := by
  have hv := besselIntervalStep_valid (224 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState224 besselGridState224_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (224 * 157 / 50) (157 / 50) 29 besselGridState224)
    (T := besselGridState225) besselGridState225_step hv
  convert hm using 1 <;> norm_num

def besselGridState226 : IntervalRat × IntervalRat :=
  (orderedInterval (308934915274059808590747371586683 / 25000000000000000000000000000000000) (1235739661096346078152898943025757 / 100000000000000000000000000000000000),
   orderedInterval (136374695288964189074860892949021 / 5000000000000000000000000000000000) (2727493905779390752609588438219183 / 100000000000000000000000000000000000))

theorem besselGridState226_step : besselStateSubset
    (besselIntervalStep (225 * 157 / 50) (157 / 50) 29 besselGridState225) besselGridState226 = true := by
  norm_num [besselGridState225, besselGridState226, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState226_valid : BesselStateValid (226 * 157 / 50 : ℚ) besselGridState226 := by
  have hv := besselIntervalStep_valid (225 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState225 besselGridState225_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (225 * 157 / 50) (157 / 50) 29 besselGridState225)
    (T := besselGridState226) besselGridState226_step hv
  convert hm using 1 <;> norm_num

def besselGridState227 : IntervalRat × IntervalRat :=
  (orderedInterval (-245735911968868276305252701332967 / 20000000000000000000000000000000000) (-61433977992211699688952376822523 / 5000000000000000000000000000000000),
   orderedInterval (-680861450773848483843109622618319 / 25000000000000000000000000000000000) (-340430725386910802527039806254501 / 12500000000000000000000000000000000))

theorem besselGridState227_step : besselStateSubset
    (besselIntervalStep (226 * 157 / 50) (157 / 50) 29 besselGridState226) besselGridState227 = true := by
  norm_num [besselGridState226, besselGridState227, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState227_valid : BesselStateValid (227 * 157 / 50 : ℚ) besselGridState227 := by
  have hv := besselIntervalStep_valid (226 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState226 besselGridState226_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (226 * 157 / 50) (157 / 50) 29 besselGridState226)
    (T := besselGridState227) besselGridState227_step hv
  convert hm using 1 <;> norm_num

def besselGridState228 : IntervalRat × IntervalRat :=
  (orderedInterval (305413328734619246663354088544041 / 25000000000000000000000000000000000) (122165331493858491906395901818061 / 10000000000000000000000000000000000),
   orderedInterval (108776869622990873188292530941871 / 4000000000000000000000000000000000) (2719421740574879889613040828965283 / 100000000000000000000000000000000000))

theorem besselGridState228_step : besselStateSubset
    (besselIntervalStep (227 * 157 / 50) (157 / 50) 29 besselGridState227) besselGridState228 = true := by
  norm_num [besselGridState227, besselGridState228, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState228_valid : BesselStateValid (228 * 157 / 50 : ℚ) besselGridState228 := by
  have hv := besselIntervalStep_valid (227 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState227 besselGridState227_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (227 * 157 / 50) (157 / 50) 29 besselGridState227)
    (T := besselGridState228) besselGridState228_step hv
  convert hm using 1 <;> norm_num

def besselGridState229 : IntervalRat × IntervalRat :=
  (orderedInterval (-1214660574652932219997869126070143 / 100000000000000000000000000000000000) (-1214660574652823742217005972694679 / 100000000000000000000000000000000000),
   orderedInterval (-2715421411343775811415511867887791 / 100000000000000000000000000000000000) (-2715421411343667206053342542403433 / 100000000000000000000000000000000000))

theorem besselGridState229_step : besselStateSubset
    (besselIntervalStep (228 * 157 / 50) (157 / 50) 29 besselGridState228) besselGridState229 = true := by
  norm_num [besselGridState228, besselGridState229, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState229_valid : BesselStateValid (229 * 157 / 50 : ℚ) besselGridState229 := by
  have hv := besselIntervalStep_valid (228 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState228 besselGridState228_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (228 * 157 / 50) (157 / 50) 29 besselGridState228)
    (T := besselGridState229) besselGridState229_step hv
  convert hm using 1 <;> norm_num

def besselGridState230 : IntervalRat × IntervalRat :=
  (orderedInterval (241540198521090711125573370319219 / 20000000000000000000000000000000000) (603850496302781289743509644943877 / 50000000000000000000000000000000000),
   orderedInterval (1355722256671280567519539895747449 / 50000000000000000000000000000000000) (542288902668534057313100538096729 / 20000000000000000000000000000000000))

theorem besselGridState230_step : besselStateSubset
    (besselIntervalStep (229 * 157 / 50) (157 / 50) 29 besselGridState229) besselGridState230 = true := by
  norm_num [besselGridState229, besselGridState230, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState230_valid : BesselStateValid (230 * 157 / 50 : ℚ) besselGridState230 := by
  have hv := besselIntervalStep_valid (229 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState229 besselGridState229_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (229 * 157 / 50) (157 / 50) 29 besselGridState229)
    (T := besselGridState230) besselGridState230_step hv
  convert hm using 1 <;> norm_num

def besselGridState231 : IntervalRat × IntervalRat :=
  (orderedInterval (-1200774227655607618352621811954439 / 100000000000000000000000000000000000) (-1200774227655498047706234906535827 / 100000000000000000000000000000000000),
   orderedInterval (-1353745374615903331649671629670247 / 50000000000000000000000000000000000) (-676872687307924241224969021304469 / 25000000000000000000000000000000000))

theorem besselGridState231_step : besselStateSubset
    (besselIntervalStep (230 * 157 / 50) (157 / 50) 29 besselGridState230) besselGridState231 = true := by
  norm_num [besselGridState230, besselGridState231, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState231_valid : BesselStateValid (231 * 157 / 50 : ℚ) besselGridState231 := by
  have hv := besselIntervalStep_valid (230 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState230 besselGridState230_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (230 * 157 / 50) (157 / 50) 29 besselGridState230)
    (T := besselGridState231) besselGridState231_step hv
  convert hm using 1 <;> norm_num

def besselGridState232 : IntervalRat × IntervalRat :=
  (orderedInterval (238775988760421558772189079129751 / 20000000000000000000000000000000000) (1193879943802217912004489725837079 / 100000000000000000000000000000000000),
   orderedInterval (2703559826298237823573647833784027 / 100000000000000000000000000000000000) (2703559826298348069555930235467727 / 100000000000000000000000000000000000))

theorem besselGridState232_step : besselStateSubset
    (besselIntervalStep (231 * 157 / 50) (157 / 50) 29 besselGridState231) besselGridState232 = true := by
  norm_num [besselGridState231, besselGridState232, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState232_valid : BesselStateValid (232 * 157 / 50 : ℚ) besselGridState232 := by
  have hv := besselIntervalStep_valid (231 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState231 besselGridState231_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (231 * 157 / 50) (157 / 50) 29 besselGridState231)
    (T := besselGridState232) besselGridState232_step hv
  convert hm using 1 <;> norm_num

def besselGridState233 : IntervalRat × IntervalRat :=
  (orderedInterval (-296754452521499977975216180580877 / 25000000000000000000000000000000000) (-1187017810085889245549260843457451 / 100000000000000000000000000000000000),
   orderedInterval (-1349825728182925166613697678184113 / 50000000000000000000000000000000000) (-674912864091434884737886292134157 / 25000000000000000000000000000000000))

theorem besselGridState233_step : besselStateSubset
    (besselIntervalStep (232 * 157 / 50) (157 / 50) 29 besselGridState232) besselGridState233 = true := by
  norm_num [besselGridState232, besselGridState233, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState233_valid : BesselStateValid (233 * 157 / 50 : ℚ) besselGridState233 := by
  have hv := besselIntervalStep_valid (232 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState232 besselGridState232_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (232 * 157 / 50) (157 / 50) 29 besselGridState232)
    (T := besselGridState233) besselGridState233_step hv
  convert hm using 1 <;> norm_num

def besselGridState234 : IntervalRat × IntervalRat :=
  (orderedInterval (295046875123161583638294493497447 / 25000000000000000000000000000000000) (1180187500492757549824724084608771 / 100000000000000000000000000000000000),
   orderedInterval (2695765355705769772206825584017149 / 100000000000000000000000000000000000) (2695765355705881115487979080845863 / 100000000000000000000000000000000000))

theorem besselGridState234_step : besselStateSubset
    (besselIntervalStep (233 * 157 / 50) (157 / 50) 29 besselGridState233) besselGridState234 = true := by
  norm_num [besselGridState233, besselGridState234, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState234_valid : BesselStateValid (234 * 157 / 50 : ℚ) besselGridState234 := by
  have hv := besselIntervalStep_valid (233 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState233 besselGridState233_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (233 * 157 / 50) (157 / 50) 29 besselGridState233)
    (T := besselGridState234) besselGridState234_step hv
  convert hm using 1 <;> norm_num

def besselGridState235 : IntervalRat × IntervalRat :=
  (orderedInterval (-293347173464868750990445105341427 / 25000000000000000000000000000000000) (-146673586732420404882178430222379 / 12500000000000000000000000000000000),
   orderedInterval (-1345950622475862772210910085835021 / 50000000000000000000000000000000000) (-1345950622475806825711321758951293 / 50000000000000000000000000000000000))

theorem besselGridState235_step : besselStateSubset
    (besselIntervalStep (234 * 157 / 50) (157 / 50) 29 besselGridState234) besselGridState235 = true := by
  norm_num [besselGridState234, besselGridState235, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState235_valid : BesselStateValid (235 * 157 / 50 : ℚ) besselGridState235 := by
  have hv := besselIntervalStep_valid (234 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState234 besselGridState234_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (234 * 157 / 50) (157 / 50) 29 besselGridState234)
    (T := besselGridState235) besselGridState235_step hv
  convert hm using 1 <;> norm_num

def besselGridState236 : IntervalRat × IntervalRat :=
  (orderedInterval (1166621073782366804123038520985539 / 100000000000000000000000000000000000) (1166621073782479119374046357939031 / 100000000000000000000000000000000000),
   orderedInterval (2688058849014008098442728440469089 / 100000000000000000000000000000000000) (537611769802824108374726757550659 / 20000000000000000000000000000000000))

theorem besselGridState236_step : besselStateSubset
    (besselIntervalStep (235 * 157 / 50) (157 / 50) 29 besselGridState235) besselGridState236 = true := by
  norm_num [besselGridState235, besselGridState236, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState236_valid : BesselStateValid (236 * 157 / 50 : ℚ) besselGridState236 := by
  have hv := besselIntervalStep_valid (235 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState235 besselGridState235_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (235 * 157 / 50) (157 / 50) 29 besselGridState235)
    (T := besselGridState236) besselGridState236_step hv
  convert hm using 1 <;> norm_num

def besselGridState237 : IntervalRat × IntervalRat :=
  (orderedInterval (-289971082131930479246040519178813 / 25000000000000000000000000000000000) (-1159884328527609050671666643692381 / 100000000000000000000000000000000000),
   orderedInterval (-1342118948499480936791103391753783 / 50000000000000000000000000000000000) (-2684237896998848879004880151247073 / 100000000000000000000000000000000000))

theorem besselGridState237_step : besselStateSubset
    (besselIntervalStep (236 * 157 / 50) (157 / 50) 29 besselGridState236) besselGridState237 = true := by
  norm_num [besselGridState236, besselGridState237, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState237_valid : BesselStateValid (237 * 157 / 50 : ℚ) besselGridState237 := by
  have hv := besselIntervalStep_valid (236 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState236 besselGridState236_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (236 * 157 / 50) (157 / 50) 29 besselGridState236)
    (T := besselGridState237) besselGridState237_step hv
  convert hm using 1 <;> norm_num

def besselGridState238 : IntervalRat × IntervalRat :=
  (orderedInterval (1153178150943012079403532568263401 / 100000000000000000000000000000000000) (115317815094312549749333448755699 / 10000000000000000000000000000000000),
   orderedInterval (670109530531704044382418422700791 / 25000000000000000000000000000000000) (670109530531732430992275655828743 / 25000000000000000000000000000000000))

theorem besselGridState238_step : besselStateSubset
    (besselIntervalStep (237 * 157 / 50) (157 / 50) 29 besselGridState237) besselGridState238 = true := by
  norm_num [besselGridState237, besselGridState238, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState238_valid : BesselStateValid (238 * 157 / 50 : ℚ) besselGridState238 := by
  have hv := besselIntervalStep_valid (237 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState237 besselGridState237_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (237 * 157 / 50) (157 / 50) 29 besselGridState237)
    (T := besselGridState238) besselGridState238_step hv
  convert hm using 1 <;> norm_num

def besselGridState239 : IntervalRat × IntervalRat :=
  (orderedInterval (-57325111918646672624862096176431 / 5000000000000000000000000000000000) (-573251119186409740956663536495303 / 50000000000000000000000000000000000),
   orderedInterval (-535331852330996061013392901476513 / 20000000000000000000000000000000000) (-535331852330973241209752492783617 / 20000000000000000000000000000000000))

theorem besselGridState239_step : besselStateSubset
    (besselIntervalStep (238 * 157 / 50) (157 / 50) 29 besselGridState238) besselGridState239 = true := by
  norm_num [besselGridState238, besselGridState239, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState239_valid : BesselStateValid (239 * 157 / 50 : ℚ) besselGridState239 := by
  have hv := besselIntervalStep_valid (238 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState238 besselGridState238_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (238 * 157 / 50) (157 / 50) 29 besselGridState238)
    (T := besselGridState239) besselGridState239_step hv
  convert hm using 1 <;> norm_num

def besselGridState240 : IntervalRat × IntervalRat :=
  (orderedInterval (227971258514780022654246865122099 / 20000000000000000000000000000000000) (113985629257401463706705751249287 / 10000000000000000000000000000000000),
   orderedInterval (534580211359907600835346143825863 / 20000000000000000000000000000000000) (2672901056799652656491367853950337 / 100000000000000000000000000000000000))

theorem besselGridState240_step : besselStateSubset
    (besselIntervalStep (239 * 157 / 50) (157 / 50) 29 besselGridState239) besselGridState240 = true := by
  norm_num [besselGridState239, besselGridState240, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState240_valid : BesselStateValid (240 * 157 / 50 : ℚ) besselGridState240 := by
  have hv := besselIntervalStep_valid (239 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState239 besselGridState239_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (239 * 157 / 50) (157 / 50) 29 besselGridState239)
    (T := besselGridState240) besselGridState240_step hv
  convert hm using 1 <;> norm_num

def besselGridState241 : IntervalRat × IntervalRat :=
  (orderedInterval (-566620009817033419369957506798967 / 50000000000000000000000000000000000) (-566620009816975880506698858854419 / 50000000000000000000000000000000000),
   orderedInterval (-667290813165535345621460349079733 / 25000000000000000000000000000000000) (-2669163252662026176156114643104599 / 100000000000000000000000000000000000))

theorem besselGridState241_step : besselStateSubset
    (besselIntervalStep (240 * 157 / 50) (157 / 50) 29 besselGridState240) besselGridState241 = true := by
  norm_num [besselGridState240, besselGridState241, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState241_valid : BesselStateValid (241 * 157 / 50 : ℚ) besselGridState241 := by
  have hv := besselIntervalStep_valid (240 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState240 besselGridState240_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (240 * 157 / 50) (157 / 50) 29 besselGridState240)
    (T := besselGridState241) besselGridState241_step hv
  convert hm using 1 <;> norm_num

def besselGridState242 : IntervalRat × IntervalRat :=
  (orderedInterval (1126653129891553867241839367608801 / 100000000000000000000000000000000000) (35207910309114671863088385070313 / 3125000000000000000000000000000000),
   orderedInterval (2665445598154971844131241565064697 / 100000000000000000000000000000000000) (533089119631017521039141277983171 / 20000000000000000000000000000000000))

theorem besselGridState242_step : besselStateSubset
    (besselIntervalStep (241 * 157 / 50) (157 / 50) 29 besselGridState241) besselGridState242 = true := by
  norm_num [besselGridState241, besselGridState242, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState242_valid : BesselStateValid (242 * 157 / 50 : ℚ) besselGridState242 := by
  have hv := besselIntervalStep_valid (241 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState241 besselGridState241_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (241 * 157 / 50) (157 / 50) 29 besselGridState241)
    (T := besselGridState242) besselGridState242_step hv
  convert hm using 1 <;> norm_num

def besselGridState243 : IntervalRat × IntervalRat :=
  (orderedInterval (-140011917232267026677080647263539 / 12500000000000000000000000000000000) (-560047668929010012834206913139691 / 50000000000000000000000000000000000),
   orderedInterval (-2661747845931041892647693240805059 / 100000000000000000000000000000000000) (-1330873922965462788063923291329951 / 50000000000000000000000000000000000))

theorem besselGridState243_step : besselStateSubset
    (besselIntervalStep (242 * 157 / 50) (157 / 50) 29 besselGridState242) besselGridState243 = true := by
  norm_num [besselGridState242, besselGridState243, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState243_valid : BesselStateValid (243 * 157 / 50 : ℚ) besselGridState243 := by
  have hv := besselIntervalStep_valid (242 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState242 besselGridState242_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (242 * 157 / 50) (157 / 50) 29 besselGridState242)
    (T := besselGridState243) besselGridState243_step hv
  convert hm using 1 <;> norm_num

def besselGridState244 : IntervalRat × IntervalRat :=
  (orderedInterval (4454265448564009944609201867329 / 400000000000000000000000000000000) (139195795267639903749192444583817 / 12500000000000000000000000000000000),
   orderedInterval (2658069752312437474832283598533131 / 100000000000000000000000000000000000) (664517438078138586882288136218273 / 25000000000000000000000000000000000))

theorem besselGridState244_step : besselStateSubset
    (besselIntervalStep (243 * 157 / 50) (157 / 50) 29 besselGridState243) besselGridState244 = true := by
  norm_num [besselGridState243, besselGridState244, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState244_valid : BesselStateValid (244 * 157 / 50 : ℚ) besselGridState244 := by
  have hv := besselIntervalStep_valid (243 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState243 besselGridState243_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (243 * 157 / 50) (157 / 50) 29 besselGridState243)
    (T := besselGridState244) besselGridState244_step hv
  convert hm using 1 <;> norm_num

def besselGridState245 : IntervalRat × IntervalRat :=
  (orderedInterval (-276766481342479914585011150044721 / 25000000000000000000000000000000000) (-110706592536980235768303641333683 / 10000000000000000000000000000000000),
   orderedInterval (-331801384652981052597894059903141 / 12500000000000000000000000000000000) (-132720553861186549559331135455129 / 5000000000000000000000000000000000))

theorem besselGridState245_step : besselStateSubset
    (besselIntervalStep (244 * 157 / 50) (157 / 50) 29 besselGridState244) besselGridState245 = true := by
  norm_num [besselGridState244, besselGridState245, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState245_valid : BesselStateValid (245 * 157 / 50 : ℚ) besselGridState245 := by
  have hv := besselIntervalStep_valid (244 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState244 besselGridState244_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (244 * 157 / 50) (157 / 50) 29 besselGridState244)
    (T := besselGridState245) besselGridState245_step hv
  convert hm using 1 <;> norm_num

def besselGridState246 : IntervalRat × IntervalRat :=
  (orderedInterval (137574219265292576108566321849883 / 12500000000000000000000000000000000) (34393554816326827095783332927871 / 3125000000000000000000000000000000),
   orderedInterval (530154316824783671393622500857503 / 20000000000000000000000000000000000) (1325385792062018172093970552257403 / 50000000000000000000000000000000000))

theorem besselGridState246_step : besselStateSubset
    (besselIntervalStep (245 * 157 / 50) (157 / 50) 29 besselGridState245) besselGridState246 = true := by
  norm_num [besselGridState245, besselGridState246, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState246_valid : BesselStateValid (246 * 157 / 50 : ℚ) besselGridState246 := by
  have hv := besselIntervalStep_valid (245 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState245 besselGridState245_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (245 * 157 / 50) (157 / 50) 29 besselGridState245)
    (T := besselGridState246) besselGridState246_step hv
  convert hm using 1 <;> norm_num

def besselGridState247 : IntervalRat × IntervalRat :=
  (orderedInterval (-21882991577077294823847965649497 / 2000000000000000000000000000000000) (-1094149578853746324731576660456611 / 100000000000000000000000000000000000),
   orderedInterval (-82723469998182355009789986522991 / 3125000000000000000000000000000000) (-2647151039941716814745513268704711 / 100000000000000000000000000000000000))

theorem besselGridState247_step : besselStateSubset
    (besselIntervalStep (246 * 157 / 50) (157 / 50) 29 besselGridState246) besselGridState247 = true := by
  norm_num [besselGridState246, besselGridState247, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState247_valid : BesselStateValid (247 * 157 / 50 : ℚ) besselGridState247 := by
  have hv := besselIntervalStep_valid (246 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState246 besselGridState246_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (246 * 157 / 50) (157 / 50) 29 besselGridState246)
    (T := besselGridState247) besselGridState247_step hv
  convert hm using 1 <;> norm_num

def besselGridState248 : IntervalRat × IntervalRat :=
  (orderedInterval (108773313382651999184909526561907 / 10000000000000000000000000000000000) (1087733133826638967299960359937813 / 100000000000000000000000000000000000),
   orderedInterval (2643549215011626063664646613822727 / 100000000000000000000000000000000000) (264354921501174516830599174196201 / 10000000000000000000000000000000000))

theorem besselGridState248_step : besselStateSubset
    (besselIntervalStep (247 * 157 / 50) (157 / 50) 29 besselGridState247) besselGridState248 = true := by
  norm_num [besselGridState247, besselGridState248, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState248_valid : BesselStateValid (248 * 157 / 50 : ℚ) besselGridState248 := by
  have hv := besselIntervalStep_valid (247 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState247 besselGridState247_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (247 * 157 / 50) (157 / 50) 29 besselGridState247)
    (T := besselGridState248) besselGridState248_step hv
  convert hm using 1 <;> norm_num

def besselGridState249 : IntervalRat × IntervalRat :=
  (orderedInterval (-270336039260587596881354068213829 / 25000000000000000000000000000000000) (-16896002453784857068089813668563 / 1562500000000000000000000000000000),
   orderedInterval (-2639965883011648201542156865243583 / 100000000000000000000000000000000000) (-2639965883011528537100588124279061 / 100000000000000000000000000000000000))

theorem besselGridState249_step : besselStateSubset
    (besselIntervalStep (248 * 157 / 50) (157 / 50) 29 besselGridState248) besselGridState249 = true := by
  norm_num [besselGridState248, besselGridState249, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState249_valid : BesselStateValid (249 * 157 / 50 : ℚ) besselGridState249 := by
  have hv := besselIntervalStep_valid (248 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState248 besselGridState248_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (248 * 157 / 50) (157 / 50) 29 besselGridState248)
    (T := besselGridState249) besselGridState249_step hv
  convert hm using 1 <;> norm_num

def besselGridState250 : IntervalRat × IntervalRat :=
  (orderedInterval (537491195087354296397699194367141 / 50000000000000000000000000000000000) (537491195087414344203816225272931 / 50000000000000000000000000000000000),
   orderedInterval (659100205225418821235643650668373 / 25000000000000000000000000000000000) (659100205225448877478004199492319 / 25000000000000000000000000000000000))

theorem besselGridState250_step : besselStateSubset
    (besselIntervalStep (249 * 157 / 50) (157 / 50) 29 besselGridState249) besselGridState250 = true := by
  norm_num [besselGridState249, besselGridState250, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState250_valid : BesselStateValid (250 * 157 / 50 : ℚ) besselGridState250 := by
  have hv := besselIntervalStep_valid (249 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState249 besselGridState249_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (249 * 157 / 50) (157 / 50) 29 besselGridState249)
    (T := besselGridState250) besselGridState250_step hv
  convert hm using 1 <;> norm_num

def besselGridState251 : IntervalRat × IntervalRat :=
  (orderedInterval (-1068647578504811474562481644899217 / 100000000000000000000000000000000000) (-267161894626172704444228600605147 / 25000000000000000000000000000000000),
   orderedInterval (-52657076177302842738527149047733 / 2000000000000000000000000000000000) (-329106726108127668837548187690713 / 12500000000000000000000000000000000))

theorem besselGridState251_step : besselStateSubset
    (besselIntervalStep (250 * 157 / 50) (157 / 50) 29 besselGridState250) besselGridState251 = true := by
  norm_num [besselGridState250, besselGridState251, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState251_valid : BesselStateValid (251 * 157 / 50 : ℚ) besselGridState251 := by
  have hv := besselIntervalStep_valid (250 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState250 besselGridState250_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (250 * 157 / 50) (157 / 50) 29 besselGridState250)
    (T := besselGridState251) besselGridState251_step hv
  convert hm using 1 <;> norm_num

def besselGridState252 : IntervalRat × IntervalRat :=
  (orderedInterval (26558486771397222566852205910713 / 2500000000000000000000000000000000) (1062339470856010121362761963910117 / 100000000000000000000000000000000000),
   orderedInterval (131466231512443780661171314658779 / 5000000000000000000000000000000000) (1314662315124498480717796083028447 / 50000000000000000000000000000000000))

theorem besselGridState252_step : besselStateSubset
    (besselIntervalStep (251 * 157 / 50) (157 / 50) 29 besselGridState251) besselGridState252 = true := by
  norm_num [besselGridState251, besselGridState252, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState252_valid : BesselStateValid (252 * 157 / 50 : ℚ) besselGridState252 := by
  have hv := besselIntervalStep_valid (251 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState251 besselGridState251_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (251 * 157 / 50) (157 / 50) 29 besselGridState251)
    (T := besselGridState252) besselGridState252_step hv
  convert hm using 1 <;> norm_num

def besselGridState253 : IntervalRat × IntervalRat :=
  (orderedInterval (-211211563906511541319992923614791 / 20000000000000000000000000000000000) (-1056057819532435925277403681244861 / 100000000000000000000000000000000000),
   orderedInterval (-2625813071507953016958966349962379 / 100000000000000000000000000000000000) (-2625813071507831106029933115343353 / 100000000000000000000000000000000000))

theorem besselGridState253_step : besselStateSubset
    (besselIntervalStep (252 * 157 / 50) (157 / 50) 29 besselGridState252) besselGridState253 = true := by
  norm_num [besselGridState252, besselGridState253, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState253_valid : BesselStateValid (253 * 157 / 50 : ℚ) besselGridState253 := by
  have hv := besselIntervalStep_valid (252 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState252 besselGridState252_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (252 * 157 / 50) (157 / 50) 29 besselGridState252)
    (T := besselGridState253) besselGridState253_step hv
  convert hm using 1 <;> norm_num

def besselGridState254 : IntervalRat × IntervalRat :=
  (orderedInterval (104980238025768144529474774157641 / 10000000000000000000000000000000000) (1049802380257803789982985466813277 / 100000000000000000000000000000000000),
   orderedInterval (1311159461073971417709292570616651 / 50000000000000000000000000000000000) (2622318922148065309796169861150791 / 100000000000000000000000000000000000))

theorem besselGridState254_step : besselStateSubset
    (besselIntervalStep (253 * 157 / 50) (157 / 50) 29 besselGridState253) besselGridState254 = true := by
  norm_num [besselGridState253, besselGridState254, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState254_valid : BesselStateValid (254 * 157 / 50 : ℚ) besselGridState254 := by
  have hv := besselIntervalStep_valid (253 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState253 besselGridState253_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (253 * 157 / 50) (157 / 50) 29 besselGridState253)
    (T := besselGridState254) besselGridState254_step hv
  convert hm using 1 <;> norm_num

def besselGridState255 : IntervalRat × IntervalRat :=
  (orderedInterval (-208714582422884368529885817511727 / 20000000000000000000000000000000000) (-13044661401428736673283933791459 / 1250000000000000000000000000000000),
   orderedInterval (-523768394934448826309162448522943 / 20000000000000000000000000000000000) (-2618841974672121092986979816879591 / 100000000000000000000000000000000000))

theorem besselGridState255_step : besselStateSubset
    (besselIntervalStep (254 * 157 / 50) (157 / 50) 29 besselGridState254) besselGridState255 = true := by
  norm_num [besselGridState254, besselGridState255, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState255_valid : BesselStateValid (255 * 157 / 50 : ℚ) besselGridState255 := by
  have hv := besselIntervalStep_valid (254 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState254 besselGridState254_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (254 * 157 / 50) (157 / 50) 29 besselGridState254)
    (T := besselGridState255) besselGridState255_step hv
  convert hm using 1 <;> norm_num

def besselGridState256 : IntervalRat × IntervalRat :=
  (orderedInterval (1037369177485672654327401551411093 / 100000000000000000000000000000000000) (207473835497159225589280839146033 / 20000000000000000000000000000000000),
   orderedInterval (2615382024526709200165731201462283 / 100000000000000000000000000000000000) (1307691012263416401819760533067469 / 50000000000000000000000000000000000))

theorem besselGridState256_step : besselStateSubset
    (besselIntervalStep (255 * 157 / 50) (157 / 50) 29 besselGridState255) besselGridState256 = true := by
  norm_num [besselGridState255, besselGridState256, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState256_valid : BesselStateValid (256 * 157 / 50 : ℚ) besselGridState256 := by
  have hv := besselIntervalStep_valid (255 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState255 besselGridState255_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (255 * 157 / 50) (157 / 50) 29 besselGridState255)
    (T := besselGridState256) besselGridState256_step hv
  convert hm using 1 <;> norm_num

def besselGridState257 : IntervalRat × IntervalRat :=
  (orderedInterval (-16112358468728996888178014241141 / 1562500000000000000000000000000000) (-515595470999265880828638617216481 / 50000000000000000000000000000000000),
   orderedInterval (-326492358756167462777540000863781 / 12500000000000000000000000000000000) (-1305969435024607766548424019708021 / 50000000000000000000000000000000000))

theorem besselGridState257_step : besselStateSubset
    (besselIntervalStep (256 * 157 / 50) (157 / 50) 29 besselGridState256) besselGridState257 = true := by
  norm_num [besselGridState256, besselGridState257, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState257_valid : BesselStateValid (257 * 157 / 50 : ℚ) besselGridState257 := by
  have hv := besselIntervalStep_valid (256 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState256 besselGridState256_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (256 * 157 / 50) (157 / 50) 29 besselGridState256)
    (T := besselGridState257) besselGridState257_step hv
  convert hm using 1 <;> norm_num

def besselGridState258 : IntervalRat × IntervalRat :=
  (orderedInterval (512518987233400161096594687066249 / 50000000000000000000000000000000000) (1025037974466924927682257471127551 / 100000000000000000000000000000000000),
   orderedInterval (2608512312417170556794905193681273 / 100000000000000000000000000000000000) (2608512312417295292303800279323701 / 100000000000000000000000000000000000))

theorem besselGridState258_step : besselStateSubset
    (besselIntervalStep (257 * 157 / 50) (157 / 50) 29 besselGridState257) besselGridState258 = true := by
  norm_num [besselGridState257, besselGridState258, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState258_valid : BesselStateValid (258 * 157 / 50 : ℚ) besselGridState258 := by
  have hv := besselIntervalStep_valid (257 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState257 besselGridState257_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (257 * 157 / 50) (157 / 50) 29 besselGridState257)
    (T := besselGridState258) besselGridState258_step hv
  convert hm using 1 <;> norm_num

def besselGridState259 : IntervalRat × IntervalRat :=
  (orderedInterval (-509455023418379015855998161608387 / 50000000000000000000000000000000000) (-509455023418316429591560179450023 / 50000000000000000000000000000000000),
   orderedInterval (-2605102155598205751767883809856497 / 100000000000000000000000000000000000) (-40704721181220007017762606501697 / 1562500000000000000000000000000000))

theorem besselGridState259_step : besselStateSubset
    (besselIntervalStep (258 * 157 / 50) (157 / 50) 29 besselGridState258) besselGridState259 = true := by
  norm_num [besselGridState258, besselGridState259, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState259_valid : BesselStateValid (259 * 157 / 50 : ℚ) besselGridState259 := by
  have hv := besselIntervalStep_valid (258 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState258 besselGridState258_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (258 * 157 / 50) (157 / 50) 29 besselGridState258)
    (T := besselGridState259) besselGridState259_step hv
  convert hm using 1 <;> norm_num

def besselGridState260 : IntervalRat × IntervalRat :=
  (orderedInterval (1012806934132605903808265714087947 / 100000000000000000000000000000000000) (1978138543227991492411762696279 / 195312500000000000000000000000000),
   orderedInterval (2601708206300449718893295386816703 / 100000000000000000000000000000000000) (2601708206300575589384332278949667 / 100000000000000000000000000000000000))

theorem besselGridState260_step : besselStateSubset
    (besselIntervalStep (259 * 157 / 50) (157 / 50) 29 besselGridState259) besselGridState260 = true := by
  norm_num [besselGridState259, besselGridState260, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState260_valid : BesselStateValid (260 * 157 / 50 : ℚ) besselGridState260 := by
  have hv := besselIntervalStep_valid (259 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState259 besselGridState259_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (259 * 157 / 50) (157 / 50) 29 besselGridState259)
    (T := besselGridState260) besselGridState260_step hv
  convert hm using 1 <;> norm_num

def besselGridState261 : IntervalRat × IntervalRat :=
  (orderedInterval (-1006728414405163186076997471684143 / 100000000000000000000000000000000000) (-50336420720251843862693397570923 / 5000000000000000000000000000000000),
   orderedInterval (-40598910530093319653943451903319 / 1562500000000000000000000000000000) (-2598330273925846018762585512501989 / 100000000000000000000000000000000000))

theorem besselGridState261_step : besselStateSubset
    (besselIntervalStep (260 * 157 / 50) (157 / 50) 29 besselGridState260) besselGridState261 = true := by
  norm_num [besselGridState260, besselGridState261, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState261_valid : BesselStateValid (261 * 157 / 50 : ℚ) besselGridState261 := by
  have hv := besselIntervalStep_valid (260 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState260 besselGridState260_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (260 * 157 / 50) (157 / 50) 29 besselGridState260)
    (T := besselGridState261) besselGridState261_step hv
  convert hm using 1 <;> norm_num

def besselGridState262 : IntervalRat × IntervalRat :=
  (orderedInterval (500337134339201223920797085306309 / 50000000000000000000000000000000000) (1000674268678529325921208745195853 / 100000000000000000000000000000000000),
   orderedInterval (2594968170521981125172431920125523 / 100000000000000000000000000000000000) (2594968170522108133600806524602489 / 100000000000000000000000000000000000))

theorem besselGridState262_step : besselStateSubset
    (besselIntervalStep (261 * 157 / 50) (157 / 50) 29 besselGridState261) besselGridState262 = true := by
  norm_num [besselGridState261, besselGridState262, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState262_valid : BesselStateValid (262 * 157 / 50 : ℚ) besselGridState262 := by
  have hv := besselIntervalStep_valid (261 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState261 besselGridState261_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (261 * 157 / 50) (157 / 50) 29 besselGridState261)
    (T := besselGridState262) besselGridState262_step hv
  convert hm using 1 <;> norm_num

def besselGridState263 : IntervalRat × IntervalRat :=
  (orderedInterval (-497322140450478373692353627532947 / 50000000000000000000000000000000000) (-497322140450414649653836721595893 / 50000000000000000000000000000000000),
   orderedInterval (-647905427684227595232261335813117 / 25000000000000000000000000000000000) (-2591621710736782802421247373250643 / 100000000000000000000000000000000000))

theorem besselGridState263_step : besselStateSubset
    (besselIntervalStep (262 * 157 / 50) (157 / 50) 29 besselGridState262) besselGridState263 = true := by
  norm_num [besselGridState262, besselGridState263, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState263_valid : BesselStateValid (263 * 157 / 50 : ℚ) besselGridState263 := by
  have hv := besselIntervalStep_valid (262 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState262 besselGridState262_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (262 * 157 / 50) (157 / 50) 29 besselGridState262)
    (T := besselGridState263) besselGridState263_step hv
  convert hm using 1 <;> norm_num

def besselGridState264 : IntervalRat × IntervalRat :=
  (orderedInterval (494319118947315506465428039622951 / 50000000000000000000000000000000000) (988638237894759031747266629860111 / 100000000000000000000000000000000000),
   orderedInterval (25882907117734329904337806857187 / 1000000000000000000000000000000000) (1294145355886780569881435559814739 / 50000000000000000000000000000000000))

theorem besselGridState264_step : besselStateSubset
    (besselIntervalStep (263 * 157 / 50) (157 / 50) 29 besselGridState263) besselGridState264 = true := by
  norm_num [besselGridState263, besselGridState264, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState264_valid : BesselStateValid (264 * 157 / 50 : ℚ) besselGridState264 := by
  have hv := besselIntervalStep_valid (263 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState263 besselGridState263_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (263 * 157 / 50) (157 / 50) 29 besselGridState263)
    (T := besselGridState264) besselGridState264_step hv
  convert hm using 1 <;> norm_num

def besselGridState265 : IntervalRat × IntervalRat :=
  (orderedInterval (-245663982326998524649026298830413 / 25000000000000000000000000000000000) (-196531185861573101659467125588253 / 20000000000000000000000000000000000),
   orderedInterval (-2584974993346477174772009375681283 / 100000000000000000000000000000000000) (-1292487496673174226939365506657831 / 50000000000000000000000000000000000))

theorem besselGridState265_step : besselStateSubset
    (besselIntervalStep (264 * 157 / 50) (157 / 50) 29 besselGridState264) besselGridState265 = true := by
  norm_num [besselGridState264, besselGridState265, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState265_valid : BesselStateValid (265 * 157 / 50 : ℚ) besselGridState265 := by
  have hv := besselIntervalStep_valid (264 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState264 besselGridState264_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (264 * 157 / 50) (157 / 50) 29 besselGridState264)
    (T := besselGridState265) besselGridState265_step hv
  convert hm using 1 <;> norm_num

def besselGridState266 : IntervalRat × IntervalRat :=
  (orderedInterval (488348573783444102955495071574547 / 50000000000000000000000000000000000) (488348573783508684218063621070887 / 50000000000000000000000000000000000),
   orderedInterval (2581674377638080706466618446358653 / 100000000000000000000000000000000000) (1290837188819104999834004004249017 / 50000000000000000000000000000000000))

theorem besselGridState266_step : besselStateSubset
    (besselIntervalStep (265 * 157 / 50) (157 / 50) 29 besselGridState265) besselGridState266 = true := by
  norm_num [besselGridState265, besselGridState266, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState266_valid : BesselStateValid (266 * 157 / 50 : ℚ) besselGridState266 := by
  have hv := besselIntervalStep_valid (265 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState265 besselGridState265_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (265 * 157 / 50) (157 / 50) 29 besselGridState265)
    (T := besselGridState266) besselGridState266_step hv
  convert hm using 1 <;> norm_num

def besselGridState267 : IntervalRat × IntervalRat :=
  (orderedInterval (-194152337566001301190746428425541 / 20000000000000000000000000000000000) (-970761687829876770457191297468481 / 100000000000000000000000000000000000),
   orderedInterval (-2578388689257242544970014159892951 / 100000000000000000000000000000000000) (-1289194344628556339357780438402767 / 50000000000000000000000000000000000))

theorem besselGridState267_step : besselStateSubset
    (besselIntervalStep (266 * 157 / 50) (157 / 50) 29 besselGridState266) besselGridState267 = true := by
  norm_num [besselGridState266, besselGridState267, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState267_valid : BesselStateValid (267 * 157 / 50 : ℚ) besselGridState267 := by
  have hv := besselIntervalStep_valid (266 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState266 besselGridState266_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (266 * 157 / 50) (157 / 50) 29 besselGridState266)
    (T := besselGridState267) besselGridState267_step hv
  convert hm using 1 <;> norm_num

def besselGridState268 : IntervalRat × IntervalRat :=
  (orderedInterval (96484934794130396711464625589847 / 10000000000000000000000000000000000) (192969869588286855265731244804463 / 20000000000000000000000000000000000),
   orderedInterval (257511775519653023110824346055963 / 10000000000000000000000000000000000) (1287558877598330335580871840587117 / 50000000000000000000000000000000000))

theorem besselGridState268_step : besselStateSubset
    (besselIntervalStep (267 * 157 / 50) (157 / 50) 29 besselGridState267) besselGridState268 = true := by
  norm_num [besselGridState267, besselGridState268, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState268_valid : BesselStateValid (268 * 157 / 50 : ℚ) besselGridState268 := by
  have hv := besselIntervalStep_valid (267 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState267 besselGridState267_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (267 * 157 / 50) (157 / 50) 29 besselGridState267)
    (T := besselGridState268) besselGridState268_step hv
  convert hm using 1 <;> norm_num

def besselGridState269 : IntervalRat × IntervalRat :=
  (orderedInterval (-479479964193733349668507076745237 / 50000000000000000000000000000000000) (-479479964193667907829219526837059 / 50000000000000000000000000000000000),
   orderedInterval (-128593070239683912135137447904217 / 5000000000000000000000000000000000) (-2571861404793547228103186439945577 / 100000000000000000000000000000000000))

theorem besselGridState269_step : besselStateSubset
    (besselIntervalStep (268 * 157 / 50) (157 / 50) 29 besselGridState268) besselGridState269 = true := by
  norm_num [besselGridState268, besselGridState269, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState269_valid : BesselStateValid (269 * 157 / 50 : ℚ) besselGridState269 := by
  have hv := besselIntervalStep_valid (268 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState268 besselGridState268_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (268 * 157 / 50) (157 / 50) 29 besselGridState268)
    (T := besselGridState269) besselGridState269_step hv
  convert hm using 1 <;> norm_num

def besselGridState270 : IntervalRat × IntervalRat :=
  (orderedInterval (476546616126066429477319989722661 / 50000000000000000000000000000000000) (95309323225226431784590831845089 / 10000000000000000000000000000000000),
   orderedInterval (642154867422465870654133701117041 / 25000000000000000000000000000000000) (2568619469689995072510208574018681 / 100000000000000000000000000000000000))

theorem besselGridState270_step : besselStateSubset
    (besselIntervalStep (269 * 157 / 50) (157 / 50) 29 besselGridState269) besselGridState270 = true := by
  norm_num [besselGridState269, besselGridState270, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState270_valid : BesselStateValid (270 * 157 / 50 : ℚ) besselGridState270 := by
  have hv := besselIntervalStep_valid (269 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState269 besselGridState269_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (269 * 157 / 50) (157 / 50) 29 besselGridState269)
    (T := besselGridState270) besselGridState270_step hv
  convert hm using 1 <;> norm_num

def besselGridState271 : IntervalRat × IntervalRat :=
  (orderedInterval (-59203066573447813086426382069637 / 6250000000000000000000000000000000) (-947249065175032974529698857159157 / 100000000000000000000000000000000000),
   orderedInterval (-1282695891896483810987727371242543 / 50000000000000000000000000000000000) (-1282695891896417728019292860407679 / 50000000000000000000000000000000000))

theorem besselGridState271_step : besselStateSubset
    (besselIntervalStep (270 * 157 / 50) (157 / 50) 29 besselGridState270) besselGridState271 = true := by
  norm_num [besselGridState270, besselGridState271, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState271_valid : BesselStateValid (271 * 157 / 50 : ℚ) besselGridState271 := by
  have hv := besselIntervalStep_valid (270 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState270 besselGridState270_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (270 * 157 / 50) (157 / 50) 29 besselGridState270)
    (T := besselGridState271) besselGridState271_step hv
  convert hm using 1 <;> norm_num

def besselGridState272 : IntervalRat × IntervalRat :=
  (orderedInterval (941427235308594750895827563104961 / 100000000000000000000000000000000000) (941427235308727362461002457186503 / 100000000000000000000000000000000000),
   orderedInterval (2562178183237440156247341168600117 / 100000000000000000000000000000000000) (512435636647514579795505189059761 / 20000000000000000000000000000000000))

theorem besselGridState272_step : besselStateSubset
    (besselIntervalStep (271 * 157 / 50) (157 / 50) 29 besselGridState271) besselGridState272 = true := by
  norm_num [besselGridState271, besselGridState272, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState272_valid : BesselStateValid (272 * 157 / 50 : ℚ) besselGridState272 := by
  have hv := besselIntervalStep_valid (271 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState271 besselGridState271_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (271 * 157 / 50) (157 / 50) 29 besselGridState271)
    (T := besselGridState272) besselGridState272_step hv
  convert hm using 1 <;> norm_num

def besselGridState273 : IntervalRat × IntervalRat :=
  (orderedInterval (-935627553277614213918179113995007 / 100000000000000000000000000000000000) (-935627553277481024889719341878643 / 100000000000000000000000000000000000),
   orderedInterval (-2558978506349146536334127970504721 / 100000000000000000000000000000000000) (-255897850634901321605946897583251 / 10000000000000000000000000000000000))

theorem besselGridState273_step : besselStateSubset
    (besselIntervalStep (272 * 157 / 50) (157 / 50) 29 besselGridState272) besselGridState273 = true := by
  norm_num [besselGridState272, besselGridState273, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState273_valid : BesselStateValid (273 * 157 / 50 : ℚ) besselGridState273 := by
  have hv := besselIntervalStep_valid (272 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState272 besselGridState272_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (272 * 157 / 50) (157 / 50) 29 besselGridState272)
    (T := besselGridState273) besselGridState273_step hv
  convert hm using 1 <;> norm_num

def besselGridState274 : IntervalRat × IntervalRat :=
  (orderedInterval (232462458034540683268470778796721 / 25000000000000000000000000000000000) (929849832138296500317899001456181 / 100000000000000000000000000000000000),
   orderedInterval (102231703744269706308916949130551 / 4000000000000000000000000000000000) (638948148401719139073563706042139 / 25000000000000000000000000000000000))

theorem besselGridState274_step : besselStateSubset
    (besselIntervalStep (273 * 157 / 50) (157 / 50) 29 besselGridState273) besselGridState274 = true := by
  norm_num [besselGridState273, besselGridState274, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState274_valid : BesselStateValid (274 * 157 / 50 : ℚ) besselGridState274 := by
  have hv := besselIntervalStep_valid (273 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState273 besselGridState273_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (273 * 157 / 50) (157 / 50) 29 besselGridState273)
    (T := besselGridState274) besselGridState274_step hv
  convert hm using 1 <;> norm_num

def besselGridState275 : IntervalRat × IntervalRat :=
  (orderedInterval (-231023471834889529020948337518333 / 25000000000000000000000000000000000) (-115511735917427971233863829709731 / 12500000000000000000000000000000000),
   orderedInterval (-1276310143804017416804463480599941 / 50000000000000000000000000000000000) (-159538767975493772249230312360311 / 6250000000000000000000000000000000))

theorem besselGridState275_step : besselStateSubset
    (besselIntervalStep (274 * 157 / 50) (157 / 50) 29 besselGridState274) besselGridState275 = true := by
  norm_num [besselGridState274, besselGridState275, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState275_valid : BesselStateValid (275 * 157 / 50 : ℚ) besselGridState275 := by
  have hv := besselIntervalStep_valid (274 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState274 besselGridState274_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (274 * 157 / 50) (157 / 50) 29 besselGridState274)
    (T := besselGridState275) besselGridState275_step hv
  convert hm using 1 <;> norm_num

def besselGridState276 : IntervalRat × IntervalRat :=
  (orderedInterval (459179768341824034070580412550497 / 50000000000000000000000000000000000) (918359536683782994077262033266043 / 100000000000000000000000000000000000),
   orderedInterval (318682679129099212943995487288069 / 12500000000000000000000000000000000) (1274730716516464380488698921885689 / 50000000000000000000000000000000000))

theorem besselGridState276_step : besselStateSubset
    (besselIntervalStep (275 * 157 / 50) (157 / 50) 29 besselGridState275) besselGridState276 = true := by
  norm_num [besselGridState275, besselGridState276, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState276_valid : BesselStateValid (276 * 157 / 50 : ℚ) besselGridState276 := by
  have hv := besselIntervalStep_valid (275 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState275 besselGridState275_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (275 * 157 / 50) (157 / 50) 29 besselGridState275)
    (T := besselGridState276) besselGridState276_step hv
  convert hm using 1 <;> norm_num

def besselGridState277 : IntervalRat × IntervalRat :=
  (orderedInterval (-57040412518062883209752132207433 / 6250000000000000000000000000000000) (-912646600288870624941320300083383 / 100000000000000000000000000000000000),
   orderedInterval (-318289484576319512099352464548449 / 12500000000000000000000000000000000) (-1273157938305210229404934429288943 / 50000000000000000000000000000000000))

theorem besselGridState277_step : besselStateSubset
    (besselIntervalStep (276 * 157 / 50) (157 / 50) 29 besselGridState276) besselGridState277 = true := by
  norm_num [besselGridState276, besselGridState277, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState277_valid : BesselStateValid (277 * 157 / 50 : ℚ) besselGridState277 := by
  have hv := besselIntervalStep_valid (276 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState276 besselGridState276_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (276 * 157 / 50) (157 / 50) 29 besselGridState276)
    (T := besselGridState277) besselGridState277_step hv
  convert hm using 1 <;> norm_num

def besselGridState278 : IntervalRat × IntervalRat :=
  (orderedInterval (45347745027578734338067517135761 / 5000000000000000000000000000000000) (906954900551710774411114804142469 / 100000000000000000000000000000000000),
   orderedInterval (2543183467084810217341557717153507 / 100000000000000000000000000000000000) (39737241673202288072537432866687 / 1562500000000000000000000000000000))

theorem besselGridState278_step : besselStateSubset
    (besselIntervalStep (277 * 157 / 50) (157 / 50) 29 besselGridState277) besselGridState278 = true := by
  norm_num [besselGridState277, besselGridState278, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState278_valid : BesselStateValid (278 * 157 / 50 : ℚ) besselGridState278 := by
  have hv := besselIntervalStep_valid (277 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState277 besselGridState277_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (277 * 157 / 50) (157 / 50) 29 besselGridState277)
    (T := besselGridState278) besselGridState278_step hv
  convert hm using 1 <;> norm_num

def besselGridState279 : IntervalRat × IntervalRat :=
  (orderedInterval (-56330266381897153424905826239367 / 6250000000000000000000000000000000) (-450642131055108892578097328464291 / 50000000000000000000000000000000000),
   orderedInterval (-2540064055182173197361562071563453 / 100000000000000000000000000000000000) (-317508006897754549498427497781889 / 12500000000000000000000000000000000))

theorem besselGridState279_step : besselStateSubset
    (besselIntervalStep (278 * 157 / 50) (157 / 50) 29 besselGridState278) besselGridState279 = true := by
  norm_num [besselGridState278, besselGridState279, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState279_valid : BesselStateValid (279 * 157 / 50 : ℚ) besselGridState279 := by
  have hv := besselIntervalStep_valid (278 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState278 besselGridState278_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (278 * 157 / 50) (157 / 50) 29 besselGridState278)
    (T := besselGridState279) besselGridState279_step hv
  convert hm using 1 <;> norm_num

def besselGridState280 : IntervalRat × IntervalRat :=
  (orderedInterval (447817255904734887936173616803641 / 50000000000000000000000000000000000) (895634511809607028265710259947937 / 100000000000000000000000000000000000),
   orderedInterval (634239373394470763028538470105497 / 25000000000000000000000000000000000) (2536957493578020436320065280449401 / 100000000000000000000000000000000000))

theorem besselGridState280_step : besselStateSubset
    (besselIntervalStep (279 * 157 / 50) (157 / 50) 29 besselGridState279) besselGridState280 = true := by
  norm_num [besselGridState279, besselGridState280, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState280_valid : BesselStateValid (280 * 157 / 50 : ℚ) besselGridState280 := by
  have hv := besselIntervalStep_valid (279 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState279 besselGridState279_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (279 * 157 / 50) (157 / 50) 29 besselGridState279)
    (T := besselGridState280) besselGridState280_step hv
  convert hm using 1 <;> norm_num

def besselGridState281 : IntervalRat × IntervalRat :=
  (orderedInterval (-890005478665284318709134798803623 / 100000000000000000000000000000000000) (-890005478665146482805128547669569 / 100000000000000000000000000000000000),
   orderedInterval (-506772727373257849814451089560881 / 20000000000000000000000000000000000) (-2533863636866151281275059818757353 / 100000000000000000000000000000000000))

theorem besselGridState281_step : besselStateSubset
    (besselIntervalStep (280 * 157 / 50) (157 / 50) 29 besselGridState280) besselGridState281 = true := by
  norm_num [besselGridState280, besselGridState281, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState281_valid : BesselStateValid (281 * 157 / 50 : ℚ) besselGridState281 := by
  have hv := besselIntervalStep_valid (280 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState280 besselGridState280_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (280 * 157 / 50) (157 / 50) 29 besselGridState280)
    (T := besselGridState281) besselGridState281_step hv
  convert hm using 1 <;> norm_num

def besselGridState282 : IntervalRat × IntervalRat :=
  (orderedInterval (442198496914911491439670001260421 / 50000000000000000000000000000000000) (884396993829961403054618134083527 / 100000000000000000000000000000000000),
   orderedInterval (316347792690948793041817633598199 / 12500000000000000000000000000000000) (1265391170763864448241793517748089 / 50000000000000000000000000000000000))

theorem besselGridState282_step : besselStateSubset
    (besselIntervalStep (281 * 157 / 50) (157 / 50) 29 besselGridState281) besselGridState282 = true := by
  norm_num [besselGridState281, besselGridState282, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState282_valid : BesselStateValid (282 * 157 / 50 : ℚ) besselGridState282 := by
  have hv := besselIntervalStep_valid (281 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState281 besselGridState281_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (281 * 157 / 50) (157 / 50) 29 besselGridState281)
    (T := besselGridState282) besselGridState282_step hv
  convert hm using 1 <;> norm_num

def besselGridState283 : IntervalRat × IntervalRat :=
  (orderedInterval (-878808890559249994883760180150601 / 100000000000000000000000000000000000) (-109851111319888873709441265145089 / 12500000000000000000000000000000000),
   orderedInterval (-1263856732949789103979360654535967 / 50000000000000000000000000000000000) (-2527713465899439070696206223515737 / 100000000000000000000000000000000000))

theorem besselGridState283_step : besselStateSubset
    (besselIntervalStep (282 * 157 / 50) (157 / 50) 29 besselGridState282) besselGridState283 = true := by
  norm_num [besselGridState282, besselGridState283, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState283_valid : BesselStateValid (283 * 157 / 50 : ℚ) besselGridState283 := by
  have hv := besselIntervalStep_valid (282 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState282 besselGridState282_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (282 * 157 / 50) (157 / 50) 29 besselGridState282)
    (T := besselGridState283) besselGridState283_step hv
  convert hm using 1 <;> norm_num

def besselGridState284 : IntervalRat × IntervalRat :=
  (orderedInterval (436620502089292601380702123461053 / 50000000000000000000000000000000000) (873241004178724793765319170975829 / 100000000000000000000000000000000000),
   orderedInterval (2524656870145563467957746717570933 / 100000000000000000000000000000000000) (126232843507285159554820193015657 / 5000000000000000000000000000000000))

theorem besselGridState284_step : besselStateSubset
    (besselIntervalStep (283 * 157 / 50) (157 / 50) 29 besselGridState283) besselGridState284 = true := by
  norm_num [besselGridState283, besselGridState284, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState284_valid : BesselStateValid (284 * 157 / 50 : ℚ) besselGridState284 := by
  have hv := besselIntervalStep_valid (283 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState283 besselGridState283_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (283 * 157 / 50) (157 / 50) 29 besselGridState283)
    (T := besselGridState284) besselGridState284_step hv
  convert hm using 1 <;> norm_num

def besselGridState285 : IntervalRat × IntervalRat :=
  (orderedInterval (-867693172051484064215318135085091 / 100000000000000000000000000000000000) (-867693172051343886651931016222631 / 100000000000000000000000000000000000),
   orderedInterval (-504322483245463430057968968752017 / 20000000000000000000000000000000000) (-2521612416227176840511317061289231 / 100000000000000000000000000000000000))

theorem besselGridState285_step : besselStateSubset
    (besselIntervalStep (284 * 157 / 50) (157 / 50) 29 besselGridState284) besselGridState285 = true := by
  norm_num [besselGridState284, besselGridState285, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState285_valid : BesselStateValid (285 * 157 / 50 : ℚ) besselGridState285 := by
  have hv := besselIntervalStep_valid (284 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState284 besselGridState284_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (284 * 157 / 50) (157 / 50) 29 besselGridState284)
    (T := besselGridState285) besselGridState285_step hv
  convert hm using 1 <;> norm_num

def besselGridState286 : IntervalRat × IntervalRat :=
  (orderedInterval (862165233546189328516070803473351 / 100000000000000000000000000000000000) (6735665887080703854716979239581 / 781250000000000000000000000000000),
   orderedInterval (2518579967874129080698250269387507 / 100000000000000000000000000000000000) (2518579967874269977881434407798189 / 100000000000000000000000000000000000))

theorem besselGridState286_step : besselStateSubset
    (besselIntervalStep (285 * 157 / 50) (157 / 50) 29 besselGridState285) besselGridState286 = true := by
  norm_num [besselGridState285, besselGridState286, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState286_valid : BesselStateValid (286 * 157 / 50 : ℚ) besselGridState286 := by
  have hv := besselIntervalStep_valid (285 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState285 besselGridState285_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (285 * 157 / 50) (157 / 50) 29 besselGridState285)
    (T := besselGridState286) besselGridState286_step hv
  convert hm using 1 <;> norm_num

def besselGridState287 : IntervalRat × IntervalRat :=
  (orderedInterval (-856657030006555550539573026793663 / 100000000000000000000000000000000000) (-856657030006414197561654440101323 / 100000000000000000000000000000000000),
   orderedInterval (-2515559390556893631834017398598079 / 100000000000000000000000000000000000) (-628889847639188036620083140620109 / 25000000000000000000000000000000000))

theorem besselGridState287_step : besselStateSubset
    (besselIntervalStep (286 * 157 / 50) (157 / 50) 29 besselGridState286) besselGridState287 = true := by
  norm_num [besselGridState286, besselGridState287, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState287_valid : BesselStateValid (287 * 157 / 50 : ℚ) besselGridState287 := by
  have hv := besselIntervalStep_valid (286 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState286 besselGridState286_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (286 * 157 / 50) (157 / 50) 29 besselGridState286)
    (T := besselGridState287) besselGridState287_step hv
  convert hm using 1 <;> norm_num

def besselGridState288 : IntervalRat × IntervalRat :=
  (orderedInterval (851168404719180191837497236470931 / 100000000000000000000000000000000000) (34046736188772885346903656302107 / 4000000000000000000000000000000000),
   orderedInterval (78517204733070283736306226352389 / 3125000000000000000000000000000000) (2512550551458391153852889238731469 / 100000000000000000000000000000000000))

theorem besselGridState288_step : besselStateSubset
    (besselIntervalStep (287 * 157 / 50) (157 / 50) 29 besselGridState287) besselGridState288 = true := by
  norm_num [besselGridState287, besselGridState288, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState288_valid : BesselStateValid (288 * 157 / 50 : ℚ) besselGridState288 := by
  have hv := besselIntervalStep_valid (287 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState287 besselGridState287_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (287 * 157 / 50) (157 / 50) 29 besselGridState287)
    (T := besselGridState288) besselGridState288_step hv
  convert hm using 1 <;> norm_num

def besselGridState289 : IntervalRat × IntervalRat :=
  (orderedInterval (-845699202885618241814760387080463 / 100000000000000000000000000000000000) (-422849601442737855177235337358119 / 50000000000000000000000000000000000),
   orderedInterval (-1254776659723878455912739458170893 / 50000000000000000000000000000000000) (-78423541232737945244656802604047 / 3125000000000000000000000000000000))

theorem besselGridState289_step : besselStateSubset
    (besselIntervalStep (288 * 157 / 50) (157 / 50) 29 besselGridState288) besselGridState289 = true := by
  norm_num [besselGridState288, besselGridState289, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState289_valid : BesselStateValid (289 * 157 / 50 : ℚ) besselGridState289 := by
  have hv := besselIntervalStep_valid (288 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState288 besselGridState288_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (288 * 157 / 50) (157 / 50) 29 besselGridState288)
    (T := besselGridState289) besselGridState289_step hv
  convert hm using 1 <;> norm_num

def besselGridState290 : IntervalRat × IntervalRat :=
  (orderedInterval (33609970863625585211721686342977 / 4000000000000000000000000000000000) (840249271590782752147609301609183 / 100000000000000000000000000000000000),
   orderedInterval (4010508104084916505917421246201 / 160000000000000000000000000000000) (2506567565053216070669249943398579 / 100000000000000000000000000000000000))

theorem besselGridState290_step : besselStateSubset
    (besselIntervalStep (289 * 157 / 50) (157 / 50) 29 besselGridState289) besselGridState290 = true := by
  norm_num [besselGridState289, besselGridState290, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState290_valid : BesselStateValid (290 * 157 / 50 : ℚ) besselGridState290 := by
  have hv := besselIntervalStep_valid (289 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState289 besselGridState289_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (289 * 157 / 50) (157 / 50) 29 besselGridState289)
    (T := besselGridState290) besselGridState290_step hv
  convert hm using 1 <;> norm_num

def besselGridState291 : IntervalRat × IntervalRat :=
  (orderedInterval (-834818459775582313988250397025119 / 100000000000000000000000000000000000) (-166963691955087720193852097346307 / 20000000000000000000000000000000000),
   orderedInterval (-2503593160436171606510637366724757 / 100000000000000000000000000000000000) (-2503593160436027760795281459443129 / 100000000000000000000000000000000000))

theorem besselGridState291_step : besselStateSubset
    (besselIntervalStep (290 * 157 / 50) (157 / 50) 29 besselGridState290) besselGridState291 = true := by
  norm_num [besselGridState290, besselGridState291, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState291_valid : BesselStateValid (291 * 157 / 50 : ℚ) besselGridState291 := by
  have hv := besselIntervalStep_valid (290 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState290 besselGridState290_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (290 * 157 / 50) (157 / 50) 29 besselGridState290)
    (T := besselGridState291) besselGridState291_step hv
  convert hm using 1 <;> norm_num

def besselGridState292 : IntervalRat × IntervalRat :=
  (orderedInterval (103675827275960698562223968844797 / 12500000000000000000000000000000000) (414703309103914946726207364510441 / 50000000000000000000000000000000000),
   orderedInterval (2500629979365503043134337453181337 / 100000000000000000000000000000000000) (2500629979365647480865347535741519 / 100000000000000000000000000000000000))

theorem besselGridState292_step : besselStateSubset
    (besselIntervalStep (291 * 157 / 50) (157 / 50) 29 besselGridState291) besselGridState292 = true := by
  norm_num [besselGridState291, besselGridState292, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState292_valid : BesselStateValid (292 * 157 / 50 : ℚ) besselGridState292 := by
  have hv := besselIntervalStep_valid (291 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState291 besselGridState291_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (291 * 157 / 50) (157 / 50) 29 besselGridState291)
    (T := besselGridState292) besselGridState292_step hv
  convert hm using 1 <;> norm_num

def besselGridState293 : IntervalRat × IntervalRat :=
  (orderedInterval (-824013599454532615693834737474351 / 100000000000000000000000000000000000) (-824013599454387718031301907270153 / 100000000000000000000000000000000000),
   orderedInterval (-2497677897193216884448564934229061 / 100000000000000000000000000000000000) (-2497677897193071853929673116205737 / 100000000000000000000000000000000000))

theorem besselGridState293_step : besselStateSubset
    (besselIntervalStep (292 * 157 / 50) (157 / 50) 29 besselGridState292) besselGridState293 = true := by
  norm_num [besselGridState292, besselGridState293, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState293_valid : BesselStateValid (293 * 157 / 50 : ℚ) besselGridState293 := by
  have hv := besselIntervalStep_valid (292 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState292 besselGridState292_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (292 * 157 / 50) (157 / 50) 29 besselGridState292)
    (T := besselGridState293) besselGridState293_step hv
  convert hm using 1 <;> norm_num

def besselGridState294 : IntervalRat × IntervalRat :=
  (orderedInterval (204659814463602941092754914421763 / 25000000000000000000000000000000000) (818639257854557255514807128431593 / 100000000000000000000000000000000000),
   orderedInterval (2494736790828259120617374419310843 / 100000000000000000000000000000000000) (124736839541420237234872233472719 / 5000000000000000000000000000000000))

theorem besselGridState294_step : besselStateSubset
    (besselIntervalStep (293 * 157 / 50) (157 / 50) 29 besselGridState293) besselGridState294 = true := by
  norm_num [besselGridState293, besselGridState294, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState294_valid : BesselStateValid (294 * 157 / 50 : ℚ) besselGridState294 := by
  have hv := besselIntervalStep_valid (293 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState293 besselGridState293_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (293 * 157 / 50) (157 / 50) 29 besselGridState293)
    (T := besselGridState294) besselGridState294_step hv
  convert hm using 1 <;> norm_num

def besselGridState295 : IntervalRat × IntervalRat :=
  (orderedInterval (-101660431186475252790405492894609 / 12500000000000000000000000000000000) (-203320862372913984230946878764719 / 25000000000000000000000000000000000),
   orderedInterval (-2491806538714553967312461287561881 / 100000000000000000000000000000000000) (-498361307742881549779369052189271 / 20000000000000000000000000000000000))

theorem besselGridState295_step : besselStateSubset
    (besselIntervalStep (294 * 157 / 50) (157 / 50) 29 besselGridState294) besselGridState295 = true := by
  norm_num [besselGridState294, besselGridState295, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState295_valid : BesselStateValid (295 * 157 / 50 : ℚ) besselGridState295 := by
  have hv := besselIntervalStep_valid (294 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState294 besselGridState294_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (294 * 157 / 50) (157 / 50) 29 besselGridState294)
    (T := besselGridState295) besselGridState295_step hv
  convert hm using 1 <;> norm_num

def besselGridState296 : IntervalRat × IntervalRat :=
  (orderedInterval (403973016084358445853067823805481 / 50000000000000000000000000000000000) (807946032168863572136746403906983 / 100000000000000000000000000000000000),
   orderedInterval (1244443510402499168428551733079499 / 50000000000000000000000000000000000) (62222175520128628759592619373231 / 2500000000000000000000000000000000))

theorem besselGridState296_step : besselStateSubset
    (besselIntervalStep (295 * 157 / 50) (157 / 50) 29 besselGridState295) besselGridState296 = true := by
  norm_num [besselGridState295, besselGridState296, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState296_valid : BesselStateValid (296 * 157 / 50 : ℚ) besselGridState296 := by
  have hv := besselIntervalStep_valid (295 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState295 besselGridState295_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (295 * 157 / 50) (157 / 50) 29 besselGridState295)
    (T := besselGridState296) besselGridState296_step hv
  convert hm using 1 <;> norm_num

def besselGridState297 : IntervalRat × IntervalRat :=
  (orderedInterval (-802626865381188457874152899661511 / 100000000000000000000000000000000000) (-802626865381041181635829862242959 / 100000000000000000000000000000000000),
   orderedInterval (-248597811854055977021864157990327 / 10000000000000000000000000000000000) (-1242989059270206180402270902957343 / 50000000000000000000000000000000000))

theorem besselGridState297_step : besselStateSubset
    (besselIntervalStep (296 * 157 / 50) (157 / 50) 29 besselGridState296) besselGridState297 = true := by
  norm_num [besselGridState296, besselGridState297, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState297_valid : BesselStateValid (297 * 157 / 50 : ℚ) besselGridState297 := by
  have hv := besselIntervalStep_valid (296 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState296 besselGridState296_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (296 * 157 / 50) (157 / 50) 29 besselGridState296)
    (T := besselGridState297) besselGridState297_step hv
  convert hm using 1 <;> norm_num

def besselGridState298 : IntervalRat × IntervalRat :=
  (orderedInterval (398662905145775313483196145941473 / 50000000000000000000000000000000000) (79732581029169849979005967571149 / 10000000000000000000000000000000000),
   orderedInterval (2483079714825129084996555834460543 / 100000000000000000000000000000000000) (620769928706319272768935613143847 / 25000000000000000000000000000000000))

theorem besselGridState298_step : besselStateSubset
    (besselIntervalStep (297 * 157 / 50) (157 / 50) 29 besselGridState297) besselGridState298 = true := by
  norm_num [besselGridState297, besselGridState298, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState298_valid : BesselStateValid (298 * 157 / 50 : ℚ) besselGridState298 := by
  have hv := besselIntervalStep_valid (297 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState297 besselGridState297_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (297 * 157 / 50) (157 / 50) 29 besselGridState297)
    (T := besselGridState298) besselGridState298_step hv
  convert hm using 1 <;> norm_num

def besselGridState299 : IntervalRat × IntervalRat :=
  (orderedInterval (-396021364852939910424649204721663 / 50000000000000000000000000000000000) (-99005341213216418832697371129217 / 12500000000000000000000000000000000),
   orderedInterval (-2480191694005495296871589575333843 / 100000000000000000000000000000000000) (-1240095847002673346674325508731923 / 50000000000000000000000000000000000))

theorem besselGridState299_step : besselStateSubset
    (besselIntervalStep (298 * 157 / 50) (157 / 50) 29 besselGridState298) besselGridState299 = true := by
  norm_num [besselGridState298, besselGridState299, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState299_valid : BesselStateValid (299 * 157 / 50 : ℚ) besselGridState299 := by
  have hv := besselIntervalStep_valid (298 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState298 besselGridState298_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (298 * 157 / 50) (157 / 50) 29 besselGridState298)
    (T := besselGridState299) besselGridState299_step hv
  convert hm using 1 <;> norm_num

def besselGridState300 : IntervalRat × IntervalRat :=
  (orderedInterval (393388744023588239508623897478437 / 50000000000000000000000000000000000) (786777488047325547348804181763509 / 100000000000000000000000000000000000),
   orderedInterval (309664242730877297506337713788587 / 12500000000000000000000000000000000) (1238656970923583790898567771786791 / 50000000000000000000000000000000000))

theorem besselGridState300_step : besselStateSubset
    (besselIntervalStep (299 * 157 / 50) (157 / 50) 29 besselGridState299) besselGridState300 = true := by
  norm_num [besselGridState299, besselGridState300, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState300_valid : BesselStateValid (300 * 157 / 50 : ℚ) besselGridState300 := by
  have hv := besselIntervalStep_valid (299 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState299 besselGridState299_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (299 * 157 / 50) (157 / 50) 29 besselGridState299)
    (T := besselGridState300) besselGridState300_step hv
  convert hm using 1 <;> norm_num

def besselGridState301 : IntervalRat × IntervalRat :=
  (orderedInterval (-781529951333722423407798145408863 / 100000000000000000000000000000000000) (-781529951333572756151541205739089 / 100000000000000000000000000000000000),
   orderedInterval (-2474446345514444168873191515583133 / 100000000000000000000000000000000000) (-154652896594643398007652456598107 / 6250000000000000000000000000000000))

theorem besselGridState301_step : besselStateSubset
    (besselIntervalStep (300 * 157 / 50) (157 / 50) 29 besselGridState300) besselGridState301 = true := by
  norm_num [besselGridState300, besselGridState301, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState301_valid : BesselStateValid (301 * 157 / 50 : ℚ) besselGridState301 := by
  have hv := besselIntervalStep_valid (300 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState300 besselGridState300_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (300 * 157 / 50) (157 / 50) 29 besselGridState300)
    (T := besselGridState301) besselGridState301_step hv
  convert hm using 1 <;> norm_num

def besselGridState302 : IntervalRat × IntervalRat :=
  (orderedInterval (776299987153121562326791618640443 / 100000000000000000000000000000000000) (776299987153271829289692973541609 / 100000000000000000000000000000000000),
   orderedInterval (1235794396774180525236385229132969 / 50000000000000000000000000000000000) (1235794396774255725504872720105883 / 50000000000000000000000000000000000))

theorem besselGridState302_step : besselStateSubset
    (besselIntervalStep (301 * 157 / 50) (157 / 50) 29 besselGridState301) besselGridState302 = true := by
  norm_num [besselGridState301, besselGridState302, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState302_valid : BesselStateValid (302 * 157 / 50 : ℚ) besselGridState302 := by
  have hv := besselIntervalStep_valid (301 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState301 besselGridState301_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (301 * 157 / 50) (157 / 50) 29 besselGridState301)
    (T := besselGridState302) besselGridState302_step hv
  convert hm using 1 <;> norm_num

def besselGridState303 : IntervalRat × IntervalRat :=
  (orderedInterval (-192771866160383982027184825297133 / 25000000000000000000000000000000000) (-77108746464138506065616787128347 / 10000000000000000000000000000000000),
   orderedInterval (-2468741175846819668314700416618597 / 100000000000000000000000000000000000) (-2468741175846668667208515443196557 / 100000000000000000000000000000000000))

theorem besselGridState303_step : besselStateSubset
    (besselIntervalStep (302 * 157 / 50) (157 / 50) 29 besselGridState302) besselGridState303 = true := by
  norm_num [besselGridState302, besselGridState303, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState303_valid : BesselStateValid (303 * 157 / 50 : ℚ) besselGridState303 := by
  have hv := besselIntervalStep_valid (302 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState302 besselGridState302_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (302 * 157 / 50) (157 / 50) 29 besselGridState302)
    (T := besselGridState303) besselGridState303_step hv
  convert hm using 1 <;> norm_num

def besselGridState304 : IntervalRat × IntervalRat :=
  (orderedInterval (23934132951829638274857122995913 / 3125000000000000000000000000000000) (95736531807337486690222305213771 / 12500000000000000000000000000000000),
   orderedInterval (2465903383642539145964812272490729 / 100000000000000000000000000000000000) (493180676728538149684855762847207 / 20000000000000000000000000000000000))

theorem besselGridState304_step : besselStateSubset
    (besselIntervalStep (303 * 157 / 50) (157 / 50) 29 besselGridState303) besselGridState304 = true := by
  norm_num [besselGridState303, besselGridState304, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState304_valid : BesselStateValid (304 * 157 / 50 : ℚ) besselGridState304 := by
  have hv := besselIntervalStep_valid (303 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState303 besselGridState303_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (303 * 157 / 50) (157 / 50) 29 besselGridState303)
    (T := besselGridState304) besselGridState304_step hv
  convert hm using 1 <;> norm_num

def besselGridState305 : IntervalRat × IntervalRat :=
  (orderedInterval (-760714228767241392713921810934101 / 100000000000000000000000000000000000) (-380357114383544660964299170527123 / 50000000000000000000000000000000000),
   orderedInterval (-1231537654742649071845992408366877 / 50000000000000000000000000000000000) (-1231537654742572969547039618578837 / 50000000000000000000000000000000000))

theorem besselGridState305_step : besselStateSubset
    (besselIntervalStep (304 * 157 / 50) (157 / 50) 29 besselGridState304) besselGridState305 = true := by
  norm_num [besselGridState304, besselGridState305, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState305_valid : BesselStateValid (305 * 157 / 50 : ℚ) besselGridState305 := by
  have hv := besselIntervalStep_valid (304 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState304 besselGridState304_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (304 * 157 / 50) (157 / 50) 29 besselGridState304)
    (T := besselGridState305) besselGridState305_step hv
  convert hm using 1 <;> norm_num

def besselGridState306 : IntervalRat × IntervalRat :=
  (orderedInterval (377776630604923020461183700120069 / 50000000000000000000000000000000000) (18888831530249967863823603942597 / 2500000000000000000000000000000000),
   orderedInterval (2460256847219857892838775195097701 / 100000000000000000000000000000000000) (2460256847220010700361364712443963 / 100000000000000000000000000000000000))

theorem besselGridState306_step : besselStateSubset
    (besselIntervalStep (305 * 157 / 50) (157 / 50) 29 besselGridState305) besselGridState306 = true := by
  norm_num [besselGridState305, besselGridState306, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState306_valid : BesselStateValid (306 * 157 / 50 : ℚ) besselGridState306 := by
  have hv := besselIntervalStep_valid (305 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState305 besselGridState305_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (305 * 157 / 50) (157 / 50) 29 besselGridState305)
    (T := besselGridState306) besselGridState306_step hv
  convert hm using 1 <;> norm_num

def besselGridState307 : IntervalRat × IntervalRat :=
  (orderedInterval (-150081845377725828480070460784589 / 20000000000000000000000000000000000) (-375204613444237932568576974677411 / 50000000000000000000000000000000000),
   orderedInterval (-2457447891969092790539190226610903 / 100000000000000000000000000000000000) (-2457447891968939379304582900937041 / 100000000000000000000000000000000000))

theorem besselGridState307_step : besselStateSubset
    (besselIntervalStep (306 * 157 / 50) (157 / 50) 29 besselGridState306) besselGridState307 = true := by
  norm_num [besselGridState306, besselGridState307, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState307_valid : BesselStateValid (307 * 157 / 50 : ℚ) besselGridState307 := by
  have hv := besselIntervalStep_valid (306 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState306 besselGridState306_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (306 * 157 / 50) (157 / 50) 29 besselGridState306)
    (T := besselGridState307) besselGridState307_step hv
  convert hm using 1 <;> norm_num

def besselGridState308 : IntervalRat × IntervalRat :=
  (orderedInterval (372641001171147746613217686479787 / 50000000000000000000000000000000000) (1164503128660077148297989332699 / 156250000000000000000000000000000),
   orderedInterval (490929668022519822463655096856157 / 20000000000000000000000000000000000) (2454648340112753128053325002058931 / 100000000000000000000000000000000000))

theorem besselGridState308_step : besselStateSubset
    (besselIntervalStep (307 * 157 / 50) (157 / 50) 29 besselGridState307) besselGridState308 = true := by
  norm_num [besselGridState307, besselGridState308, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState308_valid : BesselStateValid (308 * 157 / 50 : ℚ) besselGridState308 := by
  have hv := besselIntervalStep_valid (307 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState307 besselGridState307_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (307 * 157 / 50) (157 / 50) 29 besselGridState307)
    (T := besselGridState308) besselGridState308_step hv
  convert hm using 1 <;> norm_num

def besselGridState309 : IntervalRat × IntervalRat :=
  (orderedInterval (-92521433190956249550239636290841 / 12500000000000000000000000000000000) (-740171465527495509507010902821017 / 100000000000000000000000000000000000),
   orderedInterval (-612964522317633718572681496657291 / 25000000000000000000000000000000000) (-245185808927038025326571783473383 / 10000000000000000000000000000000000))

theorem besselGridState309_step : besselStateSubset
    (besselIntervalStep (308 * 157 / 50) (157 / 50) 29 besselGridState308) besselGridState309 = true := by
  norm_num [besselGridState308, besselGridState309, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState309_valid : BesselStateValid (309 * 157 / 50 : ℚ) besselGridState309 := by
  have hv := besselIntervalStep_valid (308 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState308 besselGridState308_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (308 * 157 / 50) (157 / 50) 29 besselGridState308)
    (T := besselGridState309) besselGridState309_step hv
  convert hm using 1 <;> norm_num

def besselGridState310 : IntervalRat × IntervalRat :=
  (orderedInterval (735077495796721098312474636361251 / 100000000000000000000000000000000000) (735077495796876191208650804726411 / 100000000000000000000000000000000000),
   orderedInterval (2449077038282884592921829033346323 / 100000000000000000000000000000000000) (612269259570759955006851466760309 / 25000000000000000000000000000000000))

theorem besselGridState310_step : besselStateSubset
    (besselIntervalStep (309 * 157 / 50) (157 / 50) 29 besselGridState309) besselGridState310 = true := by
  norm_num [besselGridState309, besselGridState310, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState310_valid : BesselStateValid (310 * 157 / 50 : ℚ) besselGridState310 := by
  have hv := besselIntervalStep_valid (309 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState309 besselGridState309_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (309 * 157 / 50) (157 / 50) 29 besselGridState309)
    (T := besselGridState310) besselGridState310_step hv
  convert hm using 1 <;> norm_num

def besselGridState311 : IntervalRat × IntervalRat :=
  (orderedInterval (-729999973879167084004730091630341 / 100000000000000000000000000000000000) (-145999994775802276863109627657077 / 20000000000000000000000000000000000),
   orderedInterval (-244630508719397960423989414939699 / 10000000000000000000000000000000000) (-489261017438764754052408686140073 / 20000000000000000000000000000000000))

theorem besselGridState311_step : besselStateSubset
    (besselIntervalStep (310 * 157 / 50) (157 / 50) 29 besselGridState310) besselGridState311 = true := by
  norm_num [besselGridState310, besselGridState311, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState311_valid : BesselStateValid (311 * 157 / 50 : ℚ) besselGridState311 := by
  have hv := besselIntervalStep_valid (310 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState310 besselGridState310_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (310 * 157 / 50) (157 / 50) 29 besselGridState310)
    (T := besselGridState311) besselGridState311_step hv
  convert hm using 1 <;> norm_num

def besselGridState312 : IntervalRat × IntervalRat :=
  (orderedInterval (724938781860089963281792364460561 / 100000000000000000000000000000000000) (724938781860246270556811679598517 / 100000000000000000000000000000000000),
   orderedInterval (610885534308097664858685360967981 / 25000000000000000000000000000000000) (610885534308136775269416989640027 / 25000000000000000000000000000000000))

theorem besselGridState312_step : besselStateSubset
    (besselIntervalStep (311 * 157 / 50) (157 / 50) 29 besselGridState311) besselGridState312 = true := by
  norm_num [besselGridState311, besselGridState312, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState312_valid : BesselStateValid (312 * 157 / 50 : ℚ) besselGridState312 := by
  have hv := besselIntervalStep_valid (311 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState311 besselGridState311_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (311 * 157 / 50) (157 / 50) 29 besselGridState311)
    (T := besselGridState312) besselGridState312_step hv
  convert hm using 1 <;> norm_num

def besselGridState313 : IntervalRat × IntervalRat :=
  (orderedInterval (-719893803163156280906736671584801 / 100000000000000000000000000000000000) (-719893803162999365251951080972067 / 100000000000000000000000000000000000),
   orderedInterval (-610197022699025317930997165436209 / 25000000000000000000000000000000000) (-610197022698986055405521544400259 / 25000000000000000000000000000000000))

theorem besselGridState313_step : besselStateSubset
    (besselIntervalStep (312 * 157 / 50) (157 / 50) 29 besselGridState312) besselGridState313 = true := by
  norm_num [besselGridState312, besselGridState313, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState313_valid : BesselStateValid (313 * 157 / 50 : ℚ) besselGridState313 := by
  have hv := besselIntervalStep_valid (312 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState312 besselGridState312_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (312 * 157 / 50) (157 / 50) 29 besselGridState312)
    (T := besselGridState313) besselGridState313_step hv
  convert hm using 1 <;> norm_num

def besselGridState314 : IntervalRat × IntervalRat :=
  (orderedInterval (357432461264536182445993653132543 / 50000000000000000000000000000000000) (178716230632307472430391747340889 / 25000000000000000000000000000000000),
   orderedInterval (304755356429125159945452379060119 / 12500000000000000000000000000000000) (152377678214572433682468592445281 / 6250000000000000000000000000000000))

theorem besselGridState314_step : besselStateSubset
    (besselIntervalStep (313 * 157 / 50) (157 / 50) 29 besselGridState313) besselGridState314 = true := by
  norm_num [besselGridState313, besselGridState314, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState314_valid : BesselStateValid (314 * 157 / 50 : ℚ) besselGridState314 := by
  have hv := besselIntervalStep_valid (313 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState313 besselGridState313_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (313 * 157 / 50) (157 / 50) 29 besselGridState313)
    (T := besselGridState314) besselGridState314_step hv
  convert hm using 1 <;> norm_num

def besselGridState315 : IntervalRat × IntervalRat :=
  (orderedInterval (-354926012999695678321755594842731 / 50000000000000000000000000000000000) (-1774630064998083054607522812531 / 250000000000000000000000000000000),
   orderedInterval (-608826580956671774651250648213351 / 25000000000000000000000000000000000) (-97412252953061153167961872462391 / 4000000000000000000000000000000000))

theorem besselGridState315_step : besselStateSubset
    (besselIntervalStep (314 * 157 / 50) (157 / 50) 29 besselGridState314) besselGridState315 = true := by
  norm_num [besselGridState314, besselGridState315, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState315_valid : BesselStateValid (315 * 157 / 50 : ℚ) besselGridState315 := by
  have hv := besselIntervalStep_valid (314 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState314 besselGridState314_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (314 * 157 / 50) (157 / 50) 29 besselGridState314)
    (T := besselGridState315) besselGridState315_step hv
  convert hm using 1 <;> norm_num

def besselGridState316 : IntervalRat × IntervalRat :=
  (orderedInterval (352427500447811048743602362797057 / 50000000000000000000000000000000000) (352427500447890421527929752024293 / 50000000000000000000000000000000000),
   orderedInterval (304072301722191331916945793347453 / 12500000000000000000000000000000000) (97303136551107581423552151037091 / 4000000000000000000000000000000000))

theorem besselGridState316_step : besselStateSubset
    (besselIntervalStep (315 * 157 / 50) (157 / 50) 29 besselGridState315) besselGridState316 = true := by
  norm_num [besselGridState315, besselGridState316, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState316_valid : BesselStateValid (316 * 157 / 50 : ℚ) besselGridState316 := by
  have hv := besselIntervalStep_valid (315 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState315 besselGridState315_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (315 * 157 / 50) (157 / 50) 29 besselGridState315)
    (T := besselGridState316) besselGridState316_step hv
  convert hm using 1 <;> norm_num

def besselGridState317 : IntervalRat × IntervalRat :=
  (orderedInterval (-21871054243865481590331606535253 / 3125000000000000000000000000000000) (-699873735803536053755469968232791 / 100000000000000000000000000000000000),
   orderedInterval (-2429859028189081658486946720761063 / 100000000000000000000000000000000000) (-2429859028188922166588118825132213 / 100000000000000000000000000000000000))

theorem besselGridState317_step : besselStateSubset
    (besselIntervalStep (316 * 157 / 50) (157 / 50) 29 besselGridState316) besselGridState317 = true := by
  norm_num [besselGridState316, besselGridState317, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState317_valid : BesselStateValid (317 * 157 / 50 : ℚ) besselGridState317 := by
  have hv := besselIntervalStep_valid (316 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState316 besselGridState316_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (316 * 157 / 50) (157 / 50) 29 besselGridState316)
    (T := besselGridState317) besselGridState317_step hv
  convert hm using 1 <;> norm_num

def besselGridState318 : IntervalRat × IntervalRat :=
  (orderedInterval (34745406027684009728401054596057 / 5000000000000000000000000000000000) (173727030138460041017272084000443 / 25000000000000000000000000000000000),
   orderedInterval (2427148075049687509201228419327063 / 100000000000000000000000000000000000) (2427148075049847613545061672280507 / 100000000000000000000000000000000000))

theorem besselGridState318_step : besselStateSubset
    (besselIntervalStep (317 * 157 / 50) (157 / 50) 29 besselGridState317) besselGridState318 = true := by
  norm_num [besselGridState317, besselGridState318, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState318_valid : BesselStateValid (318 * 157 / 50 : ℚ) besselGridState318 := by
  have hv := besselIntervalStep_valid (317 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState317 besselGridState317_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (317 * 157 / 50) (157 / 50) 29 besselGridState317)
    (T := besselGridState318) besselGridState318_step hv
  convert hm using 1 <;> norm_num

def besselGridState319 : IntervalRat × IntervalRat :=
  (orderedInterval (-344979023102441622007299921701767 / 50000000000000000000000000000000000) (-689958046204722661347060885374461 / 100000000000000000000000000000000000),
   orderedInterval (-96977818536778955097877628085201 / 4000000000000000000000000000000000) (-2424445463419313159857579559574943 / 100000000000000000000000000000000000))

theorem besselGridState319_step : besselStateSubset
    (besselIntervalStep (318 * 157 / 50) (157 / 50) 29 besselGridState318) besselGridState319 = true := by
  norm_num [besselGridState318, besselGridState319, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState319_valid : BesselStateValid (319 * 157 / 50 : ℚ) besselGridState319 := by
  have hv := besselIntervalStep_valid (318 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState318 besselGridState318_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (318 * 157 / 50) (157 / 50) 29 besselGridState318)
    (T := besselGridState319) besselGridState319_step hv
  convert hm using 1 <;> norm_num

def besselGridState320 : IntervalRat × IntervalRat :=
  (orderedInterval (34251170251307367044624891607163 / 5000000000000000000000000000000000) (342511702513154268764081382570197 / 50000000000000000000000000000000000),
   orderedInterval (1210875551706246167163164507875717 / 50000000000000000000000000000000000) (302718887926581708245356224157739 / 12500000000000000000000000000000000))

theorem besselGridState320_step : besselStateSubset
    (besselIntervalStep (319 * 157 / 50) (157 / 50) 29 besselGridState319) besselGridState320 = true := by
  norm_num [besselGridState319, besselGridState320, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState320_valid : BesselStateValid (320 * 157 / 50 : ℚ) besselGridState320 := by
  have hv := besselIntervalStep_valid (319 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState319 besselGridState319_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (319 * 157 / 50) (157 / 50) 29 besselGridState319)
    (T := besselGridState320) besselGridState320_step hv
  convert hm using 1 <;> norm_num

def besselGridState321 : IntervalRat × IntervalRat :=
  (orderedInterval (-170026022620390024573091212630333 / 25000000000000000000000000000000000) (-680104090481398286885809748734507 / 100000000000000000000000000000000000),
   orderedInterval (-604766226546064157100271251814869 / 25000000000000000000000000000000000) (-1209532453092047340957331031146609 / 50000000000000000000000000000000000))

theorem besselGridState321_step : besselStateSubset
    (besselIntervalStep (320 * 157 / 50) (157 / 50) 29 besselGridState320) besselGridState321 = true := by
  norm_num [besselGridState320, besselGridState321, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState321_valid : BesselStateValid (321 * 157 / 50 : ℚ) besselGridState321 := by
  have hv := besselIntervalStep_valid (320 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState320 besselGridState320_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (320 * 157 / 50) (157 / 50) 29 besselGridState320)
    (T := besselGridState321) besselGridState321_step hv
  convert hm using 1 <;> norm_num

def besselGridState322 : IntervalRat × IntervalRat :=
  (orderedInterval (675199997211309995497560017164079 / 100000000000000000000000000000000000) (337599998605736211239440499610309 / 50000000000000000000000000000000000),
   orderedInterval (96655471356575834610679002782929 / 4000000000000000000000000000000000) (604096695978639606851788769535079 / 25000000000000000000000000000000000))

theorem besselGridState322_step : besselStateSubset
    (besselIntervalStep (321 * 157 / 50) (157 / 50) 29 besselGridState321) besselGridState322 = true := by
  norm_num [besselGridState321, besselGridState322, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState322_valid : BesselStateValid (322 * 157 / 50 : ℚ) besselGridState322 := by
  have hv := besselIntervalStep_valid (321 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState321 besselGridState321_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (321 * 157 / 50) (157 / 50) 29 besselGridState321)
    (T := besselGridState322) besselGridState322_step hv
  convert hm using 1 <;> norm_num

def besselGridState323 : IntervalRat × IntervalRat :=
  (orderedInterval (-134062204203596170898470017838957 / 20000000000000000000000000000000000) (-670311021017817811131274410559553 / 100000000000000000000000000000000000),
   orderedInterval (-1206858324897362464905191977299441 / 50000000000000000000000000000000000) (-1930973319835649400969182434971 / 80000000000000000000000000000000))

theorem besselGridState323_step : besselStateSubset
    (besselIntervalStep (322 * 157 / 50) (157 / 50) 29 besselGridState322) besselGridState323 = true := by
  norm_num [besselGridState322, besselGridState323, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState323_valid : BesselStateValid (323 * 157 / 50 : ℚ) besselGridState323 := by
  have hv := besselIntervalStep_valid (322 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState322 besselGridState322_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (322 * 157 / 50) (157 / 50) 29 besselGridState322)
    (T := besselGridState323) besselGridState323_step hv
  convert hm using 1 <;> norm_num

def besselGridState324 : IntervalRat × IntervalRat :=
  (orderedInterval (133087411769588574069450957178013 / 20000000000000000000000000000000000) (665437058848106530894188671729949 / 100000000000000000000000000000000000),
   orderedInterval (60276360450309551529618809790379 / 2500000000000000000000000000000000) (482210883602509171409693713493199 / 20000000000000000000000000000000000))

theorem besselGridState324_step : besselStateSubset
    (besselIntervalStep (323 * 157 / 50) (157 / 50) 29 besselGridState323) besselGridState324 = true := by
  norm_num [besselGridState323, besselGridState324, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState324_valid : BesselStateValid (324 * 157 / 50 : ℚ) besselGridState324 := by
  have hv := besselIntervalStep_valid (323 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState323 besselGridState323_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (323 * 157 / 50) (157 / 50) 29 besselGridState323)
    (T := besselGridState324) besselGridState324_step hv
  convert hm using 1 <;> norm_num

def besselGridState325 : IntervalRat × IntervalRat :=
  (orderedInterval (-660578008778210399117892134101201 / 100000000000000000000000000000000000) (-660578008778046120577880244304931 / 100000000000000000000000000000000000),
   orderedInterval (-2408400003738412863304126309536777 / 100000000000000000000000000000000000) (-1204200001869124224684199199175799 / 50000000000000000000000000000000000))

theorem besselGridState325_step : besselStateSubset
    (besselIntervalStep (324 * 157 / 50) (157 / 50) 29 besselGridState324) besselGridState325 = true := by
  norm_num [besselGridState324, besselGridState325, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState325_valid : BesselStateValid (325 * 157 / 50 : ℚ) besselGridState325 := by
  have hv := besselIntervalStep_valid (324 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState324 besselGridState324_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (324 * 157 / 50) (157 / 50) 29 besselGridState324)
    (T := besselGridState325) besselGridState325_step hv
  convert hm using 1 <;> norm_num

def besselGridState326 : IntervalRat × IntervalRat :=
  (orderedInterval (131146753999669215094227693523249 / 20000000000000000000000000000000000) (163933442499627743203141509594819 / 25000000000000000000000000000000000),
   orderedInterval (120287666155568604657137016144831 / 5000000000000000000000000000000000) (2405753323111537125958800133729969 / 100000000000000000000000000000000000))

theorem besselGridState326_step : besselStateSubset
    (besselIntervalStep (325 * 157 / 50) (157 / 50) 29 besselGridState325) besselGridState326 = true := by
  norm_num [besselGridState325, besselGridState326, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState326_valid : BesselStateValid (326 * 157 / 50 : ℚ) besselGridState326 := by
  have hv := besselIntervalStep_valid (325 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState325 besselGridState325_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (325 * 157 / 50) (157 / 50) 29 besselGridState325)
    (T := besselGridState326) besselGridState326_step hv
  convert hm using 1 <;> norm_num

def besselGridState327 : IntervalRat × IntervalRat :=
  (orderedInterval (-65090424279786060763074283463401 / 10000000000000000000000000000000000) (-325452121398847545339221214587473 / 50000000000000000000000000000000000),
   orderedInterval (-600778573306600411599448618004093 / 25000000000000000000000000000000000) (-600778573306558998472990578654113 / 25000000000000000000000000000000000))

theorem besselGridState327_step : besselStateSubset
    (besselIntervalStep (326 * 157 / 50) (157 / 50) 29 besselGridState326) besselGridState327 = true := by
  norm_num [besselGridState326, besselGridState327, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState327_valid : BesselStateValid (327 * 157 / 50 : ℚ) besselGridState327 := by
  have hv := besselIntervalStep_valid (326 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState326 besselGridState326_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (326 * 157 / 50) (157 / 50) 29 besselGridState326)
    (T := besselGridState327) besselGridState327_step hv
  convert hm using 1 <;> norm_num

def besselGridState328 : IntervalRat × IntervalRat :=
  (orderedInterval (646089328548609062730026382436979 / 100000000000000000000000000000000000) (323044664274387600051888925915609 / 50000000000000000000000000000000000),
   orderedInterval (2400482832119277296671430915044637 / 100000000000000000000000000000000000) (2400482832119443569677597739630223 / 100000000000000000000000000000000000))

theorem besselGridState328_step : besselStateSubset
    (besselIntervalStep (327 * 157 / 50) (157 / 50) 29 besselGridState327) besselGridState328 = true := by
  norm_num [besselGridState327, besselGridState328, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState328_valid : BesselStateValid (328 * 157 / 50 : ℚ) besselGridState328 := by
  have hv := besselIntervalStep_valid (327 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState327 besselGridState327_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (327 * 157 / 50) (157 / 50) 29 besselGridState327)
    (T := besselGridState328) besselGridState328_step hv
  convert hm using 1 <;> norm_num

def besselGridState329 : IntervalRat × IntervalRat :=
  (orderedInterval (-40080558105794520500881284822051 / 6250000000000000000000000000000000) (-641288929692545569407197117949379 / 100000000000000000000000000000000000),
   orderedInterval (-2397858858755961939175082860004439 / 100000000000000000000000000000000000) (-599464714688948761214223895094741 / 25000000000000000000000000000000000))

theorem besselGridState329_step : besselStateSubset
    (besselIntervalStep (328 * 157 / 50) (157 / 50) 29 besselGridState328) besselGridState329 = true := by
  norm_num [besselGridState328, besselGridState329, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState329_valid : BesselStateValid (329 * 157 / 50 : ℚ) besselGridState329 := by
  have hv := besselIntervalStep_valid (328 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState328 besselGridState328_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (328 * 157 / 50) (157 / 50) 29 besselGridState328)
    (T := besselGridState329) besselGridState329_step hv
  convert hm using 1 <;> norm_num

def besselGridState330 : IntervalRat × IntervalRat :=
  (orderedInterval (636502949725425582813374459148999 / 100000000000000000000000000000000000) (636502949725592963466255054132937 / 100000000000000000000000000000000000),
   orderedInterval (598810573254269722679898143978409 / 25000000000000000000000000000000000) (2395242293017246407162611161642727 / 100000000000000000000000000000000000))

theorem besselGridState330_step : besselStateSubset
    (besselIntervalStep (329 * 157 / 50) (157 / 50) 29 besselGridState329) besselGridState330 = true := by
  norm_num [besselGridState329, besselGridState330, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState330_valid : BesselStateValid (330 * 157 / 50 : ℚ) besselGridState330 := by
  have hv := besselIntervalStep_valid (329 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState329 besselGridState329_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (329 * 157 / 50) (157 / 50) 29 besselGridState329)
    (T := besselGridState330) besselGridState330_step hv
  convert hm using 1 <;> norm_num

def besselGridState331 : IntervalRat × IntervalRat :=
  (orderedInterval (-631731293183561999763145600310823 / 100000000000000000000000000000000000) (-15793282329584849906258419441867 / 2500000000000000000000000000000000),
   orderedInterval (-2392633055687922524373006685055543 / 100000000000000000000000000000000000) (-119631652784387719249560964026681 / 5000000000000000000000000000000000))

theorem besselGridState331_step : besselStateSubset
    (besselIntervalStep (330 * 157 / 50) (157 / 50) 29 besselGridState330) besselGridState331 = true := by
  norm_num [besselGridState330, besselGridState331, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState331_valid : BesselStateValid (331 * 157 / 50 : ℚ) besselGridState331 := by
  have hv := besselIntervalStep_valid (330 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState330 besselGridState330_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (330 * 157 / 50) (157 / 50) 29 besselGridState330)
    (T := besselGridState331) besselGridState331_step hv
  convert hm using 1 <;> norm_num

def besselGridState332 : IntervalRat × IntervalRat :=
  (orderedInterval (626973865628814313104852638396511 / 100000000000000000000000000000000000) (313486932814491470146334127302083 / 50000000000000000000000000000000000),
   orderedInterval (119501553422167028398798041203379 / 5000000000000000000000000000000000) (597507767110877332777895705639087 / 25000000000000000000000000000000000))

theorem besselGridState332_step : besselStateSubset
    (besselIntervalStep (331 * 157 / 50) (157 / 50) 29 besselGridState331) besselGridState332 = true := by
  norm_num [besselGridState331, besselGridState332, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState332_valid : BesselStateValid (332 * 157 / 50 : ℚ) besselGridState332 := by
  have hv := besselIntervalStep_valid (331 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState331 besselGridState331_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (331 * 157 / 50) (157 / 50) 29 besselGridState331)
    (T := besselGridState332) besselGridState332_step hv
  convert hm using 1 <;> norm_num

def besselGridState333 : IntervalRat × IntervalRat :=
  (orderedInterval (-622230573636662202002822761804259 / 100000000000000000000000000000000000) (-311115286818246475161896340781771 / 50000000000000000000000000000000000),
   orderedInterval (-1193718126919092534707050345610641 / 50000000000000000000000000000000000) (-1193718126919007840854224228901243 / 50000000000000000000000000000000000))

theorem besselGridState333_step : besselStateSubset
    (besselIntervalStep (332 * 157 / 50) (157 / 50) 29 besselGridState332) besselGridState333 = true := by
  norm_num [besselGridState332, besselGridState333, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState333_valid : BesselStateValid (333 * 157 / 50 : ℚ) besselGridState333 := by
  have hv := besselIntervalStep_valid (332 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState332 besselGridState332_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (332 * 157 / 50) (157 / 50) 29 besselGridState332)
    (T := besselGridState333) besselGridState333_step hv
  convert hm using 1 <;> norm_num

def besselGridState334 : IntervalRat × IntervalRat :=
  (orderedInterval (308750662390064355390117183370867 / 50000000000000000000000000000000000) (154375331195074646941954324716189 / 25000000000000000000000000000000000),
   orderedInterval (2384848535292586917119547257998563 / 100000000000000000000000000000000000) (1192424267646378465106278419425483 / 50000000000000000000000000000000000))

theorem besselGridState334_step : besselStateSubset
    (besselIntervalStep (333 * 157 / 50) (157 / 50) 29 besselGridState333) besselGridState334 = true := by
  norm_num [besselGridState333, besselGridState334, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState334_valid : BesselStateValid (334 * 157 / 50 : ℚ) besselGridState334 := by
  have hv := besselIntervalStep_valid (333 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState333 besselGridState333_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (333 * 157 / 50) (157 / 50) 29 besselGridState333)
    (T := besselGridState334) besselGridState334_step hv
  convert hm using 1 <;> norm_num

def besselGridState335 : IntervalRat × IntervalRat :=
  (orderedInterval (-306393013809576790549270109421163 / 50000000000000000000000000000000000) (-612786027618983077983933714400437 / 100000000000000000000000000000000000),
   orderedInterval (-2382267837082830841525585264080579 / 100000000000000000000000000000000000) (-2382267837082660202226758143550693 / 100000000000000000000000000000000000))

theorem besselGridState335_step : besselStateSubset
    (besselIntervalStep (334 * 157 / 50) (157 / 50) 29 besselGridState334) besselGridState335 = true := by
  norm_num [besselGridState334, besselGridState335, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState335_valid : BesselStateValid (335 * 157 / 50 : ℚ) besselGridState335 := by
  have hv := besselIntervalStep_valid (334 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState334 besselGridState334_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (334 * 157 / 50) (157 / 50) 29 besselGridState334)
    (T := besselGridState335) besselGridState335_step hv
  convert hm using 1 <;> norm_num

def besselGridState336 : IntervalRat × IntervalRat :=
  (orderedInterval (76010573960595885404930313274461 / 12500000000000000000000000000000000) (304042295842469106650338626768757 / 50000000000000000000000000000000000),
   orderedInterval (237969408432700612708111309710721 / 10000000000000000000000000000000000) (2379694084327177393405352639949187 / 100000000000000000000000000000000000))

theorem besselGridState336_step : besselStateSubset
    (besselIntervalStep (335 * 157 / 50) (157 / 50) 29 besselGridState335) besselGridState336 = true := by
  norm_num [besselGridState335, besselGridState336, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState336_valid : BesselStateValid (336 * 157 / 50 : ℚ) besselGridState336 := by
  have hv := besselIntervalStep_valid (335 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState335 besselGridState335_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (335 * 157 / 50) (157 / 50) 29 besselGridState335)
    (T := besselGridState336) besselGridState336_step hv
  convert hm using 1 <;> norm_num

def besselGridState337 : IntervalRat × IntervalRat :=
  (orderedInterval (-301698463734456173701520800583957 / 50000000000000000000000000000000000) (-603396927468740589574438370282433 / 100000000000000000000000000000000000),
   orderedInterval (-594281800744072520703581982720789 / 25000000000000000000000000000000000) (-29714090037201477358049309745011 / 1250000000000000000000000000000000))

theorem besselGridState337_step : besselStateSubset
    (besselIntervalStep (336 * 157 / 50) (157 / 50) 29 besselGridState336) besselGridState337 = true := by
  norm_num [besselGridState336, besselGridState337, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState337_valid : BesselStateValid (337 * 157 / 50 : ℚ) besselGridState337 := by
  have hv := besselIntervalStep_valid (336 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState336 besselGridState336_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (336 * 157 / 50) (157 / 50) 29 besselGridState336)
    (T := besselGridState337) besselGridState337_step hv
  convert hm using 1 <;> norm_num

def besselGridState338 : IntervalRat × IntervalRat :=
  (orderedInterval (598722946409019928617669332508617 / 100000000000000000000000000000000000) (149680736602298078758879619981651 / 25000000000000000000000000000000000),
   orderedInterval (2374567119800959623998961639833571 / 100000000000000000000000000000000000) (2374567119801132146837357504735183 / 100000000000000000000000000000000000))

theorem besselGridState338_step : besselStateSubset
    (besselIntervalStep (337 * 157 / 50) (157 / 50) 29 besselGridState337) besselGridState338 = true := by
  norm_num [besselGridState337, besselGridState338, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState338_valid : BesselStateValid (338 * 157 / 50 : ℚ) besselGridState338 := by
  have hv := besselIntervalStep_valid (337 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState337 besselGridState337_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (337 * 157 / 50) (157 / 50) 29 besselGridState337)
    (T := besselGridState338) besselGridState338_step hv
  convert hm using 1 <;> norm_num

def besselGridState339 : IntervalRat × IntervalRat :=
  (orderedInterval (-37128910054891433249778639728597 / 6250000000000000000000000000000000) (-594062560878089916166346921722841 / 100000000000000000000000000000000000),
   orderedInterval (-1186006881191034167859610538590167 / 50000000000000000000000000000000000) (-2372013762381895183389803856415961 / 100000000000000000000000000000000000))

theorem besselGridState339_step : besselStateSubset
    (besselIntervalStep (338 * 157 / 50) (157 / 50) 29 besselGridState338) besselGridState339 = true := by
  norm_num [besselGridState338, besselGridState339, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState339_valid : BesselStateValid (339 * 157 / 50 : ℚ) besselGridState339 := by
  have hv := besselIntervalStep_valid (338 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState338 besselGridState338_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (338 * 157 / 50) (157 / 50) 29 besselGridState338)
    (T := besselGridState339) besselGridState339_step hv
  convert hm using 1 <;> norm_num

def besselGridState340 : IntervalRat × IntervalRat :=
  (orderedInterval (58941568417051635951086973365509 / 10000000000000000000000000000000000) (589415684170690005577399908107497 / 100000000000000000000000000000000000),
   orderedInterval (1184733529548902137785457886883363 / 50000000000000000000000000000000000) (1184733529548989029107752075086779 / 50000000000000000000000000000000000))

theorem besselGridState340_step : besselStateSubset
    (besselIntervalStep (339 * 157 / 50) (157 / 50) 29 besselGridState339) besselGridState340 = true := by
  norm_num [besselGridState339, besselGridState340, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState340_valid : BesselStateValid (340 * 157 / 50 : ℚ) besselGridState340 := by
  have hv := besselIntervalStep_valid (339 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState339 besselGridState339_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (339 * 157 / 50) (157 / 50) 29 besselGridState339)
    (T := besselGridState340) besselGridState340_step hv
  convert hm using 1 <;> norm_num

def besselGridState341 : IntervalRat × IntervalRat :=
  (orderedInterval (-292391115245514765935359802671489 / 50000000000000000000000000000000000) (-584782230490855254742471802959183 / 100000000000000000000000000000000000),
   orderedInterval (-1183463469557773205356780455962431 / 50000000000000000000000000000000000) (-2366926939115371996928508799627347 / 100000000000000000000000000000000000))

theorem besselGridState341_step : besselStateSubset
    (besselIntervalStep (340 * 157 / 50) (157 / 50) 29 besselGridState340) besselGridState341 = true := by
  norm_num [besselGridState340, besselGridState341, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState341_valid : BesselStateValid (341 * 157 / 50 : ℚ) besselGridState341 := by
  have hv := besselIntervalStep_valid (340 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState340 besselGridState340_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (340 * 157 / 50) (157 / 50) 29 besselGridState340)
    (T := besselGridState341) besselGridState341_step hv
  convert hm using 1 <;> norm_num

def besselGridState342 : IntervalRat × IntervalRat :=
  (orderedInterval (58016211494175495531691495942229 / 10000000000000000000000000000000000) (116032422988385972866664572467569 / 20000000000000000000000000000000000),
   orderedInterval (1182196666189277316412584865864487 / 50000000000000000000000000000000000) (2364393332378729678577122566028599 / 100000000000000000000000000000000000))

theorem besselGridState342_step : besselStateSubset
    (besselIntervalStep (341 * 157 / 50) (157 / 50) 29 besselGridState341) besselGridState342 = true := by
  norm_num [besselGridState341, besselGridState342, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState342_valid : BesselStateValid (342 * 157 / 50 : ℚ) besselGridState342 := by
  have hv := besselIntervalStep_valid (341 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState341 besselGridState341_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (341 * 157 / 50) (157 / 50) 29 besselGridState341)
    (T := besselGridState342) besselGridState342_step hv
  convert hm using 1 <;> norm_num

def besselGridState343 : IntervalRat × IntervalRat :=
  (orderedInterval (-287777626756211607937573607727971 / 50000000000000000000000000000000000) (-57555525351224767414299140006619 / 10000000000000000000000000000000000),
   orderedInterval (-118093308479919598662377884439899 / 5000000000000000000000000000000000) (-2361866169598216294701121112662407 / 100000000000000000000000000000000000))

theorem besselGridState343_step : besselStateSubset
    (besselIntervalStep (342 * 157 / 50) (157 / 50) 29 besselGridState342) besselGridState343 = true := by
  norm_num [besselGridState342, besselGridState343, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState343_valid : BesselStateValid (343 * 157 / 50 : ℚ) besselGridState343 := by
  have hv := besselIntervalStep_valid (342 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState342 besselGridState342_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (342 * 157 / 50) (157 / 50) 29 besselGridState342)
    (T := besselGridState343) besselGridState343_step hv
  convert hm using 1 <;> norm_num

def besselGridState344 : IntervalRat × IntervalRat :=
  (orderedInterval (285480781533113380232452645072041 / 50000000000000000000000000000000000) (142740390766600733935385951458197 / 25000000000000000000000000000000000),
   orderedInterval (2359345382241933429680411839046547 / 100000000000000000000000000000000000) (471869076448421948370012568180037 / 20000000000000000000000000000000000))

theorem besselGridState344_step : besselStateSubset
    (besselIntervalStep (343 * 157 / 50) (157 / 50) 29 besselGridState343) besselGridState344 = true := by
  norm_num [besselGridState343, besselGridState344, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState344_valid : BesselStateValid (344 * 157 / 50 : ℚ) besselGridState344 := by
  have hv := besselIntervalStep_valid (343 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState343 besselGridState343_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (343 * 157 / 50) (157 / 50) 29 besselGridState343)
    (T := besselGridState344) besselGridState344_step hv
  convert hm using 1 <;> norm_num

def besselGridState345 : IntervalRat × IntervalRat :=
  (orderedInterval (-283190480665641539759190404131557 / 50000000000000000000000000000000000) (-566380961331106269867376189639823 / 100000000000000000000000000000000000),
   orderedInterval (-1178415451262070478727840082367769 / 50000000000000000000000000000000000) (-73650965703873875338529211138711 / 3125000000000000000000000000000000))

theorem besselGridState345_step : besselStateSubset
    (besselIntervalStep (344 * 157 / 50) (157 / 50) 29 besselGridState344) besselGridState345 = true := by
  norm_num [besselGridState344, besselGridState345, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState345_valid : BesselStateValid (345 * 157 / 50 : ℚ) besselGridState345 := by
  have hv := besselIntervalStep_valid (344 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState344 besselGridState344_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (344 * 157 / 50) (157 / 50) 29 besselGridState344)
    (T := besselGridState345) besselGridState345_step hv
  convert hm using 1 <;> norm_num

def besselGridState346 : IntervalRat × IntervalRat :=
  (orderedInterval (561813366886659420904707943543429 / 100000000000000000000000000000000000) (140453341721709216440278080967033 / 25000000000000000000000000000000000),
   orderedInterval (2354322663395378285883091816144659 / 100000000000000000000000000000000000) (2354322663395555867789962543718343 / 100000000000000000000000000000000000))

theorem besselGridState346_step : besselStateSubset
    (besselIntervalStep (345 * 157 / 50) (157 / 50) 29 besselGridState345) besselGridState346 = true := by
  norm_num [besselGridState345, besselGridState346, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState346_valid : BesselStateValid (346 * 157 / 50 : ℚ) besselGridState346 := by
  have hv := besselIntervalStep_valid (345 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState345 besselGridState345_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (345 * 157 / 50) (157 / 50) 29 besselGridState345)
    (T := besselGridState346) besselGridState346_step hv
  convert hm using 1 <;> norm_num

def besselGridState347 : IntervalRat × IntervalRat :=
  (orderedInterval (-139314674788552671521408514218489 / 25000000000000000000000000000000000) (-34828668697127037824477772264643 / 6250000000000000000000000000000000),
   orderedInterval (-73494393704203945253274319744189 / 3125000000000000000000000000000000) (-2351820598534348030081598702282111 / 100000000000000000000000000000000000))

theorem besselGridState347_step : besselStateSubset
    (besselIntervalStep (346 * 157 / 50) (157 / 50) 29 besselGridState346) besselGridState347 = true := by
  norm_num [besselGridState346, besselGridState347, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState347_valid : BesselStateValid (347 * 157 / 50 : ℚ) besselGridState347 := by
  have hv := besselIntervalStep_valid (346 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState346 besselGridState346_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (346 * 157 / 50) (157 / 50) 29 besselGridState346)
    (T := besselGridState347) besselGridState347_step hv
  convert hm using 1 <;> norm_num

def besselGridState348 : IntervalRat × IntervalRat :=
  (orderedInterval (138179219596232922336146244475363 / 25000000000000000000000000000000000) (34544804899069400444343693964411 / 6250000000000000000000000000000000),
   orderedInterval (146832790146036957200957232835349 / 6250000000000000000000000000000000) (2349324642336770170188141749599159 / 100000000000000000000000000000000000))

theorem besselGridState348_step : besselStateSubset
    (besselIntervalStep (347 * 157 / 50) (157 / 50) 29 besselGridState347) besselGridState348 = true := by
  norm_num [besselGridState347, besselGridState348, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState348_valid : BesselStateValid (348 * 157 / 50 : ℚ) besselGridState348 := by
  have hv := besselIntervalStep_valid (347 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState347 besselGridState347_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (347 * 157 / 50) (157 / 50) 29 besselGridState347)
    (T := besselGridState348) besselGridState348_step hv
  convert hm using 1 <;> norm_num

def besselGridState349 : IntervalRat × IntervalRat :=
  (orderedInterval (-548187825651156772445489582559611 / 100000000000000000000000000000000000) (-548187825650977416975156733089237 / 100000000000000000000000000000000000),
   orderedInterval (-117341736495307468206181735260801 / 5000000000000000000000000000000000) (-1173417364952984935683334320391599 / 50000000000000000000000000000000000))

theorem besselGridState349_step : besselStateSubset
    (besselIntervalStep (348 * 157 / 50) (157 / 50) 29 besselGridState348) besselGridState349 = true := by
  norm_num [besselGridState348, besselGridState349, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState349_valid : BesselStateValid (349 * 157 / 50 : ℚ) besselGridState349 := by
  have hv := besselIntervalStep_valid (348 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState348 besselGridState348_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (348 * 157 / 50) (157 / 50) 29 besselGridState348)
    (T := besselGridState349) besselGridState349_step hv
  convert hm using 1 <;> norm_num

def besselGridState350 : IntervalRat × IntervalRat :=
  (orderedInterval (271835731416613393530636914978141 / 50000000000000000000000000000000000) (54367146283340678107267654781899 / 10000000000000000000000000000000000),
   orderedInterval (293043849630654522636671169054437 / 12500000000000000000000000000000000) (2344350797045416312470126500491671 / 100000000000000000000000000000000000))

theorem besselGridState350_step : besselStateSubset
    (besselIntervalStep (349 * 157 / 50) (157 / 50) 29 besselGridState349) besselGridState350 = true := by
  norm_num [besselGridState349, besselGridState350, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState350_valid : BesselStateValid (350 * 157 / 50 : ℚ) besselGridState350 := by
  have hv := besselIntervalStep_valid (349 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState349 besselGridState349_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (349 * 157 / 50) (157 / 50) 29 besselGridState349)
    (T := besselGridState350) besselGridState350_step hv
  convert hm using 1 <;> norm_num

def besselGridState351 : IntervalRat × IntervalRat :=
  (orderedInterval (-269583856306018992444295447200243 / 50000000000000000000000000000000000) (-539167712611857351499308664963967 / 100000000000000000000000000000000000),
   orderedInterval (-2341872780247108278056982167283901 / 100000000000000000000000000000000000) (-2341872780246927507223623746599081 / 100000000000000000000000000000000000))

theorem besselGridState351_step : besselStateSubset
    (besselIntervalStep (350 * 157 / 50) (157 / 50) 29 besselGridState350) besselGridState351 = true := by
  norm_num [besselGridState350, besselGridState351, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState351_valid : BesselStateValid (351 * 157 / 50 : ℚ) besselGridState351 := by
  have hv := besselIntervalStep_valid (350 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState350 besselGridState350_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (350 * 157 / 50) (157 / 50) 29 besselGridState350)
    (T := besselGridState351) besselGridState351_step hv
  convert hm using 1 <;> norm_num

def besselGridState352 : IntervalRat × IntervalRat :=
  (orderedInterval (534676498456011439519120713997663 / 100000000000000000000000000000000000) (53467649845619271312425225266357 / 10000000000000000000000000000000000),
   orderedInterval (36553134635693814304584394020607 / 1562500000000000000000000000000000) (1169700308342292763310665947679131 / 50000000000000000000000000000000000))

theorem besselGridState352_step : besselStateSubset
    (besselIntervalStep (351 * 157 / 50) (157 / 50) 29 besselGridState351) besselGridState352 = true := by
  norm_num [besselGridState351, besselGridState352, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState352_valid : BesselStateValid (352 * 157 / 50 : ℚ) besselGridState352 := by
  have hv := besselIntervalStep_valid (351 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState351 besselGridState351_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (351 * 157 / 50) (157 / 50) 29 besselGridState351)
    (T := besselGridState352) besselGridState352_step hv
  convert hm using 1 <;> norm_num

def besselGridState353 : IntervalRat × IntervalRat :=
  (orderedInterval (-530197744613979294624526940443077 / 100000000000000000000000000000000000) (-106039548922759475992882896451661 / 20000000000000000000000000000000000),
   orderedInterval (-1168467122101605532046306300828781 / 50000000000000000000000000000000000) (-2336934244203029011830976233190303 / 100000000000000000000000000000000000))

theorem besselGridState353_step : besselStateSubset
    (besselIntervalStep (352 * 157 / 50) (157 / 50) 29 besselGridState352) besselGridState353 = true := by
  norm_num [besselGridState352, besselGridState353, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState353_valid : BesselStateValid (353 * 157 / 50 : ℚ) besselGridState353 := by
  have hv := besselIntervalStep_valid (352 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState352 besselGridState352_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (352 * 157 / 50) (157 / 50) 29 besselGridState352)
    (T := besselGridState353) besselGridState353_step hv
  convert hm using 1 <;> norm_num

def besselGridState354 : IntervalRat × IntervalRat :=
  (orderedInterval (65716422012805606780739411388409 / 12500000000000000000000000000000000) (262865688051313705400651876156849 / 50000000000000000000000000000000000),
   orderedInterval (291809200163935821407371849268603 / 12500000000000000000000000000000000) (2334473601311669265494614389580719 / 100000000000000000000000000000000000))

theorem besselGridState354_step : besselStateSubset
    (besselIntervalStep (353 * 157 / 50) (157 / 50) 29 besselGridState353) besselGridState354 = true := by
  norm_num [besselGridState353, besselGridState354, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState354_valid : BesselStateValid (354 * 157 / 50 : ℚ) besselGridState354 := by
  have hv := besselIntervalStep_valid (353 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState353 besselGridState353_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (353 * 157 / 50) (157 / 50) 29 besselGridState353)
    (T := besselGridState354) besselGridState354_step hv
  convert hm using 1 <;> norm_num

def besselGridState355 : IntervalRat × IntervalRat :=
  (orderedInterval (-52127731869879477239675067095667 / 10000000000000000000000000000000000) (-32579832418663223319039124188123 / 6250000000000000000000000000000000),
   orderedInterval (-2332018627173420828224650969701107 / 100000000000000000000000000000000000) (-583004656793309372793386212423993 / 25000000000000000000000000000000000))

theorem besselGridState355_step : besselStateSubset
    (besselIntervalStep (354 * 157 / 50) (157 / 50) 29 besselGridState354) besselGridState355 = true := by
  norm_num [besselGridState354, besselGridState355, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState355_valid : BesselStateValid (355 * 157 / 50 : ℚ) besselGridState355 := by
  have hv := besselIntervalStep_valid (354 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState354 besselGridState354_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (354 * 157 / 50) (157 / 50) 29 besselGridState354)
    (T := besselGridState355) besselGridState355_step hv
  convert hm using 1 <;> norm_num

def besselGridState356 : IntervalRat × IntervalRat :=
  (orderedInterval (16151109341526204038007199976939 / 3125000000000000000000000000000000) (64604437366127796510964790914079 / 12500000000000000000000000000000000),
   orderedInterval (1164784630799053778105436547058043 / 50000000000000000000000000000000000) (465913852319658307384015291495533 / 20000000000000000000000000000000000))

theorem besselGridState356_step : besselStateSubset
    (besselIntervalStep (355 * 157 / 50) (157 / 50) 29 besselGridState355) besselGridState356 = true := by
  norm_num [besselGridState355, besselGridState356, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState356_valid : BesselStateValid (356 * 157 / 50 : ℚ) besselGridState356 := by
  have hv := besselIntervalStep_valid (355 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState355 besselGridState355_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (355 * 157 / 50) (157 / 50) 29 besselGridState355)
    (T := besselGridState356) besselGridState356_step hv
  convert hm using 1 <;> norm_num

def besselGridState357 : IntervalRat × IntervalRat :=
  (orderedInterval (-102481168812067124491661242801121 / 20000000000000000000000000000000000) (-512405844060151135163659550983237 / 100000000000000000000000000000000000),
   orderedInterval (-29089068062927404753374468717529 / 1250000000000000000000000000000000) (-581781361258501938764714272031677 / 25000000000000000000000000000000000))

theorem besselGridState357_step : besselStateSubset
    (besselIntervalStep (356 * 157 / 50) (157 / 50) 29 besselGridState356) besselGridState357 = true := by
  norm_num [besselGridState356, besselGridState357, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState357_valid : BesselStateValid (357 * 157 / 50 : ℚ) besselGridState357 := by
  have hv := besselIntervalStep_valid (356 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState356 besselGridState356_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (356 * 157 / 50) (157 / 50) 29 besselGridState356)
    (T := besselGridState357) besselGridState357_step hv
  convert hm using 1 <;> norm_num

def besselGridState358 : IntervalRat × IntervalRat :=
  (orderedInterval (101597656418160722487987477434891 / 20000000000000000000000000000000000) (101597656418197749000541683166759 / 20000000000000000000000000000000000),
   orderedInterval (1162343559279391670725512568896581 / 50000000000000000000000000000000000) (23246871185589686120089931444141 / 1000000000000000000000000000000000))

theorem besselGridState358_step : besselStateSubset
    (besselIntervalStep (357 * 157 / 50) (157 / 50) 29 besselGridState357) besselGridState358 = true := by
  norm_num [besselGridState357, besselGridState358, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState358_valid : BesselStateValid (358 * 157 / 50 : ℚ) besselGridState358 := by
  have hv := besselIntervalStep_valid (357 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState357 besselGridState357_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (357 * 157 / 50) (157 / 50) 29 besselGridState357)
    (T := besselGridState358) besselGridState358_step hv
  convert hm using 1 <;> norm_num

def besselGridState359 : IntervalRat × IntervalRat :=
  (orderedInterval (-125895685435337457657657485059577 / 25000000000000000000000000000000000) (-503582741741164051953597102749307 / 100000000000000000000000000000000000),
   orderedInterval (-1161127111936187699487725302724873 / 50000000000000000000000000000000000) (-23222542238721894822244720335771 / 1000000000000000000000000000000000))

theorem besselGridState359_step : besselStateSubset
    (besselIntervalStep (358 * 157 / 50) (157 / 50) 29 besselGridState358) besselGridState359 = true := by
  norm_num [besselGridState358, besselGridState359, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState359_valid : BesselStateValid (359 * 157 / 50 : ℚ) besselGridState359 := by
  have hv := besselIntervalStep_valid (358 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState358 besselGridState358_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (358 * 157 / 50) (157 / 50) 29 besselGridState358)
    (T := besselGridState359) besselGridState359_step hv
  convert hm using 1 <;> norm_num

def besselGridState360 : IntervalRat × IntervalRat :=
  (orderedInterval (499189152444737620029084295522987 / 100000000000000000000000000000000000) (31199322027807752854230617045801 / 6250000000000000000000000000000000),
   orderedInterval (463965340657598236953271192762363 / 20000000000000000000000000000000000) (231982670328817774855766215542367 / 10000000000000000000000000000000000))

theorem besselGridState360_step : besselStateSubset
    (besselIntervalStep (359 * 157 / 50) (157 / 50) 29 besselGridState359) besselGridState360 = true := by
  norm_num [besselGridState359, besselGridState360, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState360_valid : BesselStateValid (360 * 157 / 50 : ℚ) besselGridState360 := by
  have hv := besselIntervalStep_valid (359 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState359 besselGridState359_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (359 * 157 / 50) (157 / 50) 29 besselGridState359)
    (T := besselGridState360) besselGridState360_step hv
  convert hm using 1 <;> norm_num

def besselGridState361 : IntervalRat × IntervalRat :=
  (orderedInterval (-494807444339512509607168355685709 / 100000000000000000000000000000000000) (-123701861084831359039625985637529 / 25000000000000000000000000000000000),
   orderedInterval (-2317404499726372456126262235241969 / 100000000000000000000000000000000000) (-2317404499726185244446135610209021 / 100000000000000000000000000000000000))

theorem besselGridState361_step : besselStateSubset
    (besselIntervalStep (360 * 157 / 50) (157 / 50) 29 besselGridState360) besselGridState361 = true := by
  norm_num [besselGridState360, besselGridState361, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState361_valid : BesselStateValid (361 * 157 / 50 : ℚ) besselGridState361 := by
  have hv := besselIntervalStep_valid (360 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState360 besselGridState360_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (360 * 157 / 50) (157 / 50) 29 besselGridState360)
    (T := besselGridState361) besselGridState361_step hv
  convert hm using 1 <;> norm_num

def besselGridState362 : IntervalRat × IntervalRat :=
  (orderedInterval (61304693532289587475213633734333 / 12500000000000000000000000000000000) (490437548258504421910095260517889 / 100000000000000000000000000000000000),
   orderedInterval (578746889176335499941011885756107 / 25000000000000000000000000000000000) (2314987556705529860182664849477853 / 100000000000000000000000000000000000))

theorem besselGridState362_step : besselStateSubset
    (besselIntervalStep (361 * 157 / 50) (157 / 50) 29 besselGridState361) besselGridState362 = true := by
  norm_num [besselGridState361, besselGridState362, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState362_valid : BesselStateValid (362 * 157 / 50 : ℚ) besselGridState362 := by
  have hv := besselIntervalStep_valid (361 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState361 besselGridState361_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (361 * 157 / 50) (157 / 50) 29 besselGridState361)
    (T := besselGridState362) besselGridState362_step hv
  convert hm using 1 <;> norm_num

def besselGridState363 : IntervalRat × IntervalRat :=
  (orderedInterval (-486079395722300064999954527670473 / 100000000000000000000000000000000000) (-19443175828884467735240203601849 / 4000000000000000000000000000000000),
   orderedInterval (-1156287909167626619489113092345731 / 50000000000000000000000000000000000) (-462515163667012945794053767373013 / 20000000000000000000000000000000000))

theorem besselGridState363_step : besselStateSubset
    (besselIntervalStep (362 * 157 / 50) (157 / 50) 29 besselGridState362) besselGridState363 = true := by
  norm_num [besselGridState362, besselGridState363, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState363_valid : BesselStateValid (363 * 157 / 50 : ℚ) besselGridState363 := by
  have hv := besselIntervalStep_valid (362 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState362 besselGridState362_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (362 * 157 / 50) (157 / 50) 29 besselGridState362)
    (T := besselGridState363) besselGridState363_step hv
  convert hm using 1 <;> norm_num

def besselGridState364 : IntervalRat × IntervalRat :=
  (orderedInterval (120433229732418334326417716454879 / 25000000000000000000000000000000000) (240866459464931179643602616379647 / 50000000000000000000000000000000000),
   orderedInterval (2310169229308564566852848282636839 / 100000000000000000000000000000000000) (1155084614654376863651087911946289 / 50000000000000000000000000000000000))

theorem besselGridState364_step : besselStateSubset
    (besselIntervalStep (363 * 157 / 50) (157 / 50) 29 besselGridState363) besselGridState364 = true := by
  norm_num [besselGridState363, besselGridState364, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState364_valid : BesselStateValid (364 * 157 / 50 : ℚ) besselGridState364 := by
  have hv := besselIntervalStep_valid (363 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState363 besselGridState363_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (363 * 157 / 50) (157 / 50) 29 besselGridState363)
    (T := besselGridState364) besselGridState364_step hv
  convert hm using 1 <;> norm_num

def besselGridState365 : IntervalRat × IntervalRat :=
  (orderedInterval (-238699025375197346808761891129761 / 50000000000000000000000000000000000) (-477398050750205020420200903380423 / 100000000000000000000000000000000000),
   orderedInterval (-1153883867447769338013981522052549 / 50000000000000000000000000000000000) (-576941933723837216071013170647791 / 25000000000000000000000000000000000))

theorem besselGridState365_step : besselStateSubset
    (besselIntervalStep (364 * 157 / 50) (157 / 50) 29 besselGridState364) besselGridState365 = true := by
  norm_num [besselGridState364, besselGridState365, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState365_valid : BesselStateValid (365 * 157 / 50 : ℚ) besselGridState365 := by
  have hv := besselIntervalStep_valid (364 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState364 besselGridState364_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (364 * 157 / 50) (157 / 50) 29 besselGridState364)
    (T := besselGridState365) besselGridState365_step hv
  convert hm using 1 <;> norm_num

def besselGridState366 : IntervalRat × IntervalRat :=
  (orderedInterval (236537362357476237863957716963809 / 50000000000000000000000000000000000) (473074724715142800995413997549439 / 100000000000000000000000000000000000),
   orderedInterval (2305371280934020955981680967622629 / 100000000000000000000000000000000000) (461074256186842283974914187237049 / 20000000000000000000000000000000000))

theorem besselGridState366_step : besselStateSubset
    (besselIntervalStep (365 * 157 / 50) (157 / 50) 29 besselGridState365) besselGridState366 = true := by
  norm_num [besselGridState365, besselGridState366, besselStateSubset, rationalIntervalSubset,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, linearInterval, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.scale,
    IntervalRat.mul]

theorem besselGridState366_valid : BesselStateValid (366 * 157 / 50 : ℚ) besselGridState366 := by
  have hv := besselIntervalStep_valid (365 * 157 / 50) (157 / 50) (by norm_num) 29
      besselGridState365 besselGridState365_valid
  have hm := BesselStateValid.mono
    (S := besselIntervalStep (365 * 157 / 50) (157 / 50) 29 besselGridState365)
    (T := besselGridState366) besselGridState366_step hv
  convert hm using 1 <;> norm_num

end Erdos232
