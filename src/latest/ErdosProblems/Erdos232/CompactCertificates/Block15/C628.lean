/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate628 : CompactCertificate where
  left := 499
  right := 500
  center := 999 / 2
  grid := fun i =>
    match i.val with
    | 0 => 159
    | 1 => 117
    | 2 => 189
    | 3 => 34
    | 4 => 92
    | 5 => 249
    | 6 => 184
    | 7 => 315
    | 8 => 232
    | 9 => 356
    | 10 => 205
    | 11 => 364
    | 12 => 340
    | 13 => 243
    | 14 => 276
    | 15 => 230
    | 16 => 203
    | 17 => 294
    | 18 => 163
    | 19 => 138
    | 20 => 86
    | 21 => 46
    | 22 => 126
    | 23 => 172
    | 24 => 73
    | 25 => 296
    | _ => 198
  point := fun i =>
    match i.val with
    | 0 => 999 / 2
    | 1 => 1471717756953099 / 4000000000000
    | 2 => 475923284249067 / 800000000000
    | 3 => 429443570962593 / 4000000000000
    | 4 => 1153545837840621 / 4000000000000
    | 5 => 3132101346360057 / 4000000000000
    | 6 => 2307091675682241 / 4000000000000
    | 7 => 3953240909399493 / 4000000000000
    | 8 => 2911939361297487 / 4000000000000
    | 9 => 4467663819044001 / 4000000000000
    | 10 => 2579406908573529 / 4000000000000
    | 11 => 4577202823530861 / 4000000000000
    | 12 => 4276616616876609 / 4000000000000
    | 13 => 3051995412839697 / 4000000000000
    | 14 => 3460637513521863 / 4000000000000
    | 15 => 2885118769177047 / 4000000000000
    | 16 => 2549089929441987 / 4000000000000
    | 17 => 738825617104713 / 800000000000
    | 18 => 2043630539173611 / 4000000000000
    | 19 => 1732408240645971 / 4000000000000
    | 20 => 1084060638702513 / 4000000000000
    | 21 => 583011416917071 / 4000000000000
    | 22 => 1582989408804213 / 4000000000000
    | 23 => 2161436703794901 / 4000000000000
    | 24 => 913939361297487 / 4000000000000
    | 25 => 3715112763278127 / 4000000000000
    | _ => 2481523152447393 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-24901316935 / 1000000000000) (-24901316934 / 1000000000000), orderedInterval (-25557069227 / 1000000000000) (-25557069226 / 1000000000000))
    | 1 => (orderedInterval (-37936478519 / 1000000000000) (-37936478518 / 1000000000000), orderedInterval (-17010079546 / 1000000000000) (-17010079545 / 1000000000000))
    | 2 => (orderedInterval (-30644618278 / 1000000000000) (-30644580123 / 1000000000000), orderedInterval (11472565248 / 1000000000000) (11472603403 / 1000000000000))
    | 3 => (orderedInterval (74800439968 / 1000000000000) (74800439970 / 1000000000000), orderedInterval (17942484584 / 1000000000000) (17942484585 / 1000000000000))
    | 4 => (orderedInterval (6784221665 / 1000000000000) (6784221666 / 1000000000000), orderedInterval (46480179116 / 1000000000000) (46480179117 / 1000000000000))
    | 5 => (orderedInterval (-28509584989 / 1000000000000) (-28509582641 / 1000000000000), orderedInterval (-460573161 / 1000000000000) (-460570813 / 1000000000000))
    | 6 => (orderedInterval (-15780406368 / 1000000000000) (-15780406096 / 1000000000000), orderedInterval (29249626115 / 1000000000000) (29249626387 / 1000000000000))
    | 7 => (orderedInterval (12305436494 / 1000000000000) (12305436510 / 1000000000000), orderedInterval (-22203658065 / 1000000000000) (-22203658049 / 1000000000000))
    | 8 => (orderedInterval (-2346390947 / 1000000000000) (-2346390946 / 1000000000000), orderedInterval (29480257611 / 1000000000000) (29480257612 / 1000000000000))
    | 9 => (orderedInterval (-15484841455 / 1000000000000) (-15484841339 / 1000000000000), orderedInterval (18178330052 / 1000000000000) (18178330168 / 1000000000000))
    | 10 => (orderedInterval (-31395597811 / 1000000000000) (-31395595795 / 1000000000000), orderedInterval (1269552525 / 1000000000000) (1269554542 / 1000000000000))
    | 11 => (orderedInterval (23579748758 / 1000000000000) (23579763283 / 1000000000000), orderedInterval (568156408 / 1000000000000) (568170933 / 1000000000000))
    | 12 => (orderedInterval (23774883129 / 1000000000000) (23774982252 / 1000000000000), orderedInterval (-5506157845 / 1000000000000) (-5506058721 / 1000000000000))
    | 13 => (orderedInterval (-10635608912 / 1000000000000) (-10635608911 / 1000000000000), orderedInterval (-26849114632 / 1000000000000) (-26849114631 / 1000000000000))
    | 14 => (orderedInterval (-24590339888 / 1000000000000) (-24590287101 / 1000000000000), orderedInterval (11466582173 / 1000000000000) (11466634961 / 1000000000000))
    | 15 => (orderedInterval (-14279566487 / 1000000000000) (-14279566377 / 1000000000000), orderedInterval (26062144109 / 1000000000000) (26062144219 / 1000000000000))
    | 16 => (orderedInterval (-9773473874 / 1000000000000) (-9773473873 / 1000000000000), orderedInterval (-30049863846 / 1000000000000) (-30049863845 / 1000000000000))
    | 17 => (orderedInterval (16692996718 / 1000000000000) (16692996719 / 1000000000000), orderedInterval (20256091175 / 1000000000000) (20256091176 / 1000000000000))
    | 18 => (orderedInterval (13316388026 / 1000000000000) (13316388124 / 1000000000000), orderedInterval (-32704479356 / 1000000000000) (-32704479258 / 1000000000000))
    | 19 => (orderedInterval (13052202996 / 1000000000000) (13052202997 / 1000000000000), orderedInterval (36034173083 / 1000000000000) (36034173084 / 1000000000000))
    | 20 => (orderedInterval (48400287062 / 1000000000000) (48400287295 / 1000000000000), orderedInterval (-2624500917 / 1000000000000) (-2624500684 / 1000000000000))
    | 21 => (orderedInterval (59413548240 / 1000000000000) (59413559296 / 1000000000000), orderedInterval (-29148885654 / 1000000000000) (-29148874598 / 1000000000000))
    | 22 => (orderedInterval (25584633361 / 1000000000000) (25584633362 / 1000000000000), orderedInterval (30855841322 / 1000000000000) (30855841323 / 1000000000000))
    | 23 => (orderedInterval (24392026540 / 1000000000000) (24392026541 / 1000000000000), orderedInterval (24126361693 / 1000000000000) (24126361694 / 1000000000000))
    | 24 => (orderedInterval (3511426461 / 1000000000000) (3511426468 / 1000000000000), orderedInterval (-52675924117 / 1000000000000) (-52675924110 / 1000000000000))
    | 25 => (orderedInterval (-8927444672 / 1000000000000) (-8927444669 / 1000000000000), orderedInterval (24616565551 / 1000000000000) (24616565553 / 1000000000000))
    | _ => (orderedInterval (-24471288188 / 1000000000000) (-24471273873 / 1000000000000), orderedInterval (20691729762 / 1000000000000) (20691744078 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12021765849 / 1000000000000) (-12021763574 / 1000000000000)
      | 1 => orderedInterval (1462908003 / 1000000000000) (1462908230 / 1000000000000)
      | 2 => orderedInterval (-436256550 / 1000000000000) (-436256521 / 1000000000000)
      | 3 => orderedInterval (3777314017 / 1000000000000) (3777316450 / 1000000000000)
      | 4 => orderedInterval (-1310504473 / 1000000000000) (-1310502356 / 1000000000000)
      | 5 => orderedInterval (821814340 / 1000000000000) (821814390 / 1000000000000)
      | 6 => orderedInterval (-1292259532 / 1000000000000) (-1292259383 / 1000000000000)
      | 7 => orderedInterval (-3546890751 / 1000000000000) (-3546890487 / 1000000000000)
      | _ => orderedInterval (5339337949 / 1000000000000) (5339340774 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-9444870353 / 1000000000000) (-9444867647 / 1000000000000)
      | 1 => orderedInterval (989291615 / 1000000000000) (989291945 / 1000000000000)
      | 2 => orderedInterval (2393430020 / 1000000000000) (2393430070 / 1000000000000)
      | 3 => orderedInterval (-6916192500 / 1000000000000) (-6916187121 / 1000000000000)
      | 4 => orderedInterval (-3766022067 / 1000000000000) (-3766017677 / 1000000000000)
      | 5 => orderedInterval (3587465798 / 1000000000000) (3587465869 / 1000000000000)
      | 6 => orderedInterval (3533845881 / 1000000000000) (3533846017 / 1000000000000)
      | 7 => orderedInterval (-2397829173 / 1000000000000) (-2397829059 / 1000000000000)
      | _ => orderedInterval (-8693067691 / 1000000000000) (-8693064161 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12631508096 / 1000000000000) (12631511323 / 1000000000000)
      | 1 => orderedInterval (-5027613946 / 1000000000000) (-5027613440 / 1000000000000)
      | 2 => orderedInterval (1601539243 / 1000000000000) (1601539332 / 1000000000000)
      | 3 => orderedInterval (-27458512185 / 1000000000000) (-27458500107 / 1000000000000)
      | 4 => orderedInterval (3947362140 / 1000000000000) (3947371309 / 1000000000000)
      | 5 => orderedInterval (-2034819912 / 1000000000000) (-2034819806 / 1000000000000)
      | 6 => orderedInterval (2312024980 / 1000000000000) (2312025109 / 1000000000000)
      | 7 => orderedInterval (2650278481 / 1000000000000) (2650278553 / 1000000000000)
      | _ => orderedInterval (-9582238244 / 1000000000000) (-9582233806 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9030595218 / 1000000000000) (9030599059 / 1000000000000)
      | 1 => orderedInterval (-440731822 / 1000000000000) (-440731037 / 1000000000000)
      | 2 => orderedInterval (-7513623802 / 1000000000000) (-7513623641 / 1000000000000)
      | 3 => orderedInterval (34994742146 / 1000000000000) (34994769472 / 1000000000000)
      | 4 => orderedInterval (8368120354 / 1000000000000) (8368139580 / 1000000000000)
      | 5 => orderedInterval (-7751270131 / 1000000000000) (-7751269968 / 1000000000000)
      | 6 => orderedInterval (-4257165972 / 1000000000000) (-4257165847 / 1000000000000)
      | 7 => orderedInterval (2670351776 / 1000000000000) (2670351836 / 1000000000000)
      | _ => orderedInterval (20369825469 / 1000000000000) (20369831067 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13628432434 / 1000000000000) (-13628427852 / 1000000000000)
      | 1 => orderedInterval (12266888326 / 1000000000000) (12266889555 / 1000000000000)
      | 2 => orderedInterval (-6042759325 / 1000000000000) (-6042759026 / 1000000000000)
      | 3 => orderedInterval (154510685300 / 1000000000000) (154510747482 / 1000000000000)
      | 4 => orderedInterval (-13398481185 / 1000000000000) (-13398440673 / 1000000000000)
      | 5 => orderedInterval (5790619281 / 1000000000000) (5790619539 / 1000000000000)
      | 6 => orderedInterval (-2594413795 / 1000000000000) (-2594413671 / 1000000000000)
      | 7 => orderedInterval (-2807610577 / 1000000000000) (-2807610517 / 1000000000000)
      | _ => orderedInterval (19531795412 / 1000000000000) (19531802537 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-7206302846 / 1000000000000) (-7206292477 / 1000000000000)
    | 1 => orderedInterval (-20713948470 / 1000000000000) (-20713931764 / 1000000000000)
    | 2 => orderedInterval (-20960471347 / 1000000000000) (-20960441533 / 1000000000000)
    | 3 => orderedInterval (55470843236 / 1000000000000) (55470900521 / 1000000000000)
    | _ => orderedInterval (153628291003 / 1000000000000) (153628407374 / 1000000000000)

theorem compactCertificate628_stateChecks0 :
    compactCertificate628.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (999 / 2)) (orderedInterval (-24901316935 / 1000000000000) (-24901316934 / 1000000000000), orderedInterval (-25557069227 / 1000000000000) (-25557069226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1471717756953099 / 4000000000000)) (orderedInterval (-37936478519 / 1000000000000) (-37936478518 / 1000000000000), orderedInterval (-17010079546 / 1000000000000) (-17010079545 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (475923284249067 / 800000000000)) (orderedInterval (-30644618278 / 1000000000000) (-30644580123 / 1000000000000), orderedInterval (11472565248 / 1000000000000) (11472603403 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_stateChecks1 :
    compactCertificate628.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (429443570962593 / 4000000000000)) (orderedInterval (74800439968 / 1000000000000) (74800439970 / 1000000000000), orderedInterval (17942484584 / 1000000000000) (17942484585 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1153545837840621 / 4000000000000)) (orderedInterval (6784221665 / 1000000000000) (6784221666 / 1000000000000), orderedInterval (46480179116 / 1000000000000) (46480179117 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3132101346360057 / 4000000000000)) (orderedInterval (-28509584989 / 1000000000000) (-28509582641 / 1000000000000), orderedInterval (-460573161 / 1000000000000) (-460570813 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_stateChecks2 :
    compactCertificate628.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2307091675682241 / 4000000000000)) (orderedInterval (-15780406368 / 1000000000000) (-15780406096 / 1000000000000), orderedInterval (29249626115 / 1000000000000) (29249626387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 315 12 (3953240909399493 / 4000000000000)) (orderedInterval (12305436494 / 1000000000000) (12305436510 / 1000000000000), orderedInterval (-22203658065 / 1000000000000) (-22203658049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2911939361297487 / 4000000000000)) (orderedInterval (-2346390947 / 1000000000000) (-2346390946 / 1000000000000), orderedInterval (29480257611 / 1000000000000) (29480257612 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_stateChecks3 :
    compactCertificate628.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 356 12 (4467663819044001 / 4000000000000)) (orderedInterval (-15484841455 / 1000000000000) (-15484841339 / 1000000000000), orderedInterval (18178330052 / 1000000000000) (18178330168 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2579406908573529 / 4000000000000)) (orderedInterval (-31395597811 / 1000000000000) (-31395595795 / 1000000000000), orderedInterval (1269552525 / 1000000000000) (1269554542 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 364 12 (4577202823530861 / 4000000000000)) (orderedInterval (23579748758 / 1000000000000) (23579763283 / 1000000000000), orderedInterval (568156408 / 1000000000000) (568170933 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_stateChecks4 :
    compactCertificate628.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 340 12 (4276616616876609 / 4000000000000)) (orderedInterval (23774883129 / 1000000000000) (23774982252 / 1000000000000), orderedInterval (-5506157845 / 1000000000000) (-5506058721 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3051995412839697 / 4000000000000)) (orderedInterval (-10635608912 / 1000000000000) (-10635608911 / 1000000000000), orderedInterval (-26849114632 / 1000000000000) (-26849114631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (3460637513521863 / 4000000000000)) (orderedInterval (-24590339888 / 1000000000000) (-24590287101 / 1000000000000), orderedInterval (11466582173 / 1000000000000) (11466634961 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_stateChecks5 :
    compactCertificate628.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2885118769177047 / 4000000000000)) (orderedInterval (-14279566487 / 1000000000000) (-14279566377 / 1000000000000), orderedInterval (26062144109 / 1000000000000) (26062144219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2549089929441987 / 4000000000000)) (orderedInterval (-9773473874 / 1000000000000) (-9773473873 / 1000000000000), orderedInterval (-30049863846 / 1000000000000) (-30049863845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (738825617104713 / 800000000000)) (orderedInterval (16692996718 / 1000000000000) (16692996719 / 1000000000000), orderedInterval (20256091175 / 1000000000000) (20256091176 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_stateChecks6 :
    compactCertificate628.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2043630539173611 / 4000000000000)) (orderedInterval (13316388026 / 1000000000000) (13316388124 / 1000000000000), orderedInterval (-32704479356 / 1000000000000) (-32704479258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1732408240645971 / 4000000000000)) (orderedInterval (13052202996 / 1000000000000) (13052202997 / 1000000000000), orderedInterval (36034173083 / 1000000000000) (36034173084 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1084060638702513 / 4000000000000)) (orderedInterval (48400287062 / 1000000000000) (48400287295 / 1000000000000), orderedInterval (-2624500917 / 1000000000000) (-2624500684 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_stateChecks7 :
    compactCertificate628.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (583011416917071 / 4000000000000)) (orderedInterval (59413548240 / 1000000000000) (59413559296 / 1000000000000), orderedInterval (-29148885654 / 1000000000000) (-29148874598 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1582989408804213 / 4000000000000)) (orderedInterval (25584633361 / 1000000000000) (25584633362 / 1000000000000), orderedInterval (30855841322 / 1000000000000) (30855841323 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2161436703794901 / 4000000000000)) (orderedInterval (24392026540 / 1000000000000) (24392026541 / 1000000000000), orderedInterval (24126361693 / 1000000000000) (24126361694 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_stateChecks8 :
    compactCertificate628.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (913939361297487 / 4000000000000)) (orderedInterval (3511426461 / 1000000000000) (3511426468 / 1000000000000), orderedInterval (-52675924117 / 1000000000000) (-52675924110 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 296 12 (3715112763278127 / 4000000000000)) (orderedInterval (-8927444672 / 1000000000000) (-8927444669 / 1000000000000), orderedInterval (24616565551 / 1000000000000) (24616565553 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2481523152447393 / 4000000000000)) (orderedInterval (-24471288188 / 1000000000000) (-24471273873 / 1000000000000), orderedInterval (20691729762 / 1000000000000) (20691744078 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_states : ∀ j,
    BesselStateValid (compactCertificate628.point j) (compactCertificate628.state j) :=
  compactCertificate628.statesValid_of_checks3 compactCertificate628_stateChecks0
    compactCertificate628_stateChecks1 compactCertificate628_stateChecks2
    compactCertificate628_stateChecks3 compactCertificate628_stateChecks4
    compactCertificate628_stateChecks5 compactCertificate628_stateChecks6
    compactCertificate628_stateChecks7 compactCertificate628_stateChecks8

theorem compactCertificate628_chunkChecks0_0 :
    compactCertificate628.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (999 / 2) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24901316935 / 1000000000000) (-24901316934 / 1000000000000), orderedInterval (-25557069227 / 1000000000000) (-25557069226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1471717756953099 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37936478519 / 1000000000000) (-37936478518 / 1000000000000), orderedInterval (-17010079546 / 1000000000000) (-17010079545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (475923284249067 / 800000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30644618278 / 1000000000000) (-30644580123 / 1000000000000), orderedInterval (11472565248 / 1000000000000) (11472603403 / 1000000000000)))) (orderedInterval (-12021765849 / 1000000000000) (-12021763574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (429443570962593 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74800439968 / 1000000000000) (74800439970 / 1000000000000), orderedInterval (17942484584 / 1000000000000) (17942484585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1153545837840621 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6784221665 / 1000000000000) (6784221666 / 1000000000000), orderedInterval (46480179116 / 1000000000000) (46480179117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3132101346360057 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28509584989 / 1000000000000) (-28509582641 / 1000000000000), orderedInterval (-460573161 / 1000000000000) (-460570813 / 1000000000000)))) (orderedInterval (1462908003 / 1000000000000) (1462908230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2307091675682241 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15780406368 / 1000000000000) (-15780406096 / 1000000000000), orderedInterval (29249626115 / 1000000000000) (29249626387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3953240909399493 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12305436494 / 1000000000000) (12305436510 / 1000000000000), orderedInterval (-22203658065 / 1000000000000) (-22203658049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2911939361297487 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2346390947 / 1000000000000) (-2346390946 / 1000000000000), orderedInterval (29480257611 / 1000000000000) (29480257612 / 1000000000000)))) (orderedInterval (-436256550 / 1000000000000) (-436256521 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks0_1 :
    compactCertificate628.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4467663819044001 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15484841455 / 1000000000000) (-15484841339 / 1000000000000), orderedInterval (18178330052 / 1000000000000) (18178330168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2579406908573529 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31395597811 / 1000000000000) (-31395595795 / 1000000000000), orderedInterval (1269552525 / 1000000000000) (1269554542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4577202823530861 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23579748758 / 1000000000000) (23579763283 / 1000000000000), orderedInterval (568156408 / 1000000000000) (568170933 / 1000000000000)))) (orderedInterval (3777314017 / 1000000000000) (3777316450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4276616616876609 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23774883129 / 1000000000000) (23774982252 / 1000000000000), orderedInterval (-5506157845 / 1000000000000) (-5506058721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3051995412839697 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10635608912 / 1000000000000) (-10635608911 / 1000000000000), orderedInterval (-26849114632 / 1000000000000) (-26849114631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3460637513521863 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24590339888 / 1000000000000) (-24590287101 / 1000000000000), orderedInterval (11466582173 / 1000000000000) (11466634961 / 1000000000000)))) (orderedInterval (-1310504473 / 1000000000000) (-1310502356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2885118769177047 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14279566487 / 1000000000000) (-14279566377 / 1000000000000), orderedInterval (26062144109 / 1000000000000) (26062144219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2549089929441987 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9773473874 / 1000000000000) (-9773473873 / 1000000000000), orderedInterval (-30049863846 / 1000000000000) (-30049863845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (738825617104713 / 800000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16692996718 / 1000000000000) (16692996719 / 1000000000000), orderedInterval (20256091175 / 1000000000000) (20256091176 / 1000000000000)))) (orderedInterval (821814340 / 1000000000000) (821814390 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks0_2 :
    compactCertificate628.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2043630539173611 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13316388026 / 1000000000000) (13316388124 / 1000000000000), orderedInterval (-32704479356 / 1000000000000) (-32704479258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1732408240645971 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13052202996 / 1000000000000) (13052202997 / 1000000000000), orderedInterval (36034173083 / 1000000000000) (36034173084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1084060638702513 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48400287062 / 1000000000000) (48400287295 / 1000000000000), orderedInterval (-2624500917 / 1000000000000) (-2624500684 / 1000000000000)))) (orderedInterval (-1292259532 / 1000000000000) (-1292259383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (583011416917071 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59413548240 / 1000000000000) (59413559296 / 1000000000000), orderedInterval (-29148885654 / 1000000000000) (-29148874598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1582989408804213 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25584633361 / 1000000000000) (25584633362 / 1000000000000), orderedInterval (30855841322 / 1000000000000) (30855841323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2161436703794901 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24392026540 / 1000000000000) (24392026541 / 1000000000000), orderedInterval (24126361693 / 1000000000000) (24126361694 / 1000000000000)))) (orderedInterval (-3546890751 / 1000000000000) (-3546890487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (913939361297487 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3511426461 / 1000000000000) (3511426468 / 1000000000000), orderedInterval (-52675924117 / 1000000000000) (-52675924110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3715112763278127 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8927444672 / 1000000000000) (-8927444669 / 1000000000000), orderedInterval (24616565551 / 1000000000000) (24616565553 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2481523152447393 / 4000000000000) 0 (IntervalRat.scale (999 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24471288188 / 1000000000000) (-24471273873 / 1000000000000), orderedInterval (20691729762 / 1000000000000) (20691744078 / 1000000000000)))) (orderedInterval (5339337949 / 1000000000000) (5339340774 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks0 :
    compactCertificate628.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate628.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate628_chunkChecks0_0
    compactCertificate628_chunkChecks0_1 compactCertificate628_chunkChecks0_2

theorem compactCertificate628_chunkChecks1_0 :
    compactCertificate628.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (999 / 2) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24901316935 / 1000000000000) (-24901316934 / 1000000000000), orderedInterval (-25557069227 / 1000000000000) (-25557069226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1471717756953099 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37936478519 / 1000000000000) (-37936478518 / 1000000000000), orderedInterval (-17010079546 / 1000000000000) (-17010079545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (475923284249067 / 800000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30644618278 / 1000000000000) (-30644580123 / 1000000000000), orderedInterval (11472565248 / 1000000000000) (11472603403 / 1000000000000)))) (orderedInterval (-9444870353 / 1000000000000) (-9444867647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (429443570962593 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74800439968 / 1000000000000) (74800439970 / 1000000000000), orderedInterval (17942484584 / 1000000000000) (17942484585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1153545837840621 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6784221665 / 1000000000000) (6784221666 / 1000000000000), orderedInterval (46480179116 / 1000000000000) (46480179117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3132101346360057 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28509584989 / 1000000000000) (-28509582641 / 1000000000000), orderedInterval (-460573161 / 1000000000000) (-460570813 / 1000000000000)))) (orderedInterval (989291615 / 1000000000000) (989291945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2307091675682241 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15780406368 / 1000000000000) (-15780406096 / 1000000000000), orderedInterval (29249626115 / 1000000000000) (29249626387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3953240909399493 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12305436494 / 1000000000000) (12305436510 / 1000000000000), orderedInterval (-22203658065 / 1000000000000) (-22203658049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2911939361297487 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2346390947 / 1000000000000) (-2346390946 / 1000000000000), orderedInterval (29480257611 / 1000000000000) (29480257612 / 1000000000000)))) (orderedInterval (2393430020 / 1000000000000) (2393430070 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks1_1 :
    compactCertificate628.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4467663819044001 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15484841455 / 1000000000000) (-15484841339 / 1000000000000), orderedInterval (18178330052 / 1000000000000) (18178330168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2579406908573529 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31395597811 / 1000000000000) (-31395595795 / 1000000000000), orderedInterval (1269552525 / 1000000000000) (1269554542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4577202823530861 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23579748758 / 1000000000000) (23579763283 / 1000000000000), orderedInterval (568156408 / 1000000000000) (568170933 / 1000000000000)))) (orderedInterval (-6916192500 / 1000000000000) (-6916187121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4276616616876609 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23774883129 / 1000000000000) (23774982252 / 1000000000000), orderedInterval (-5506157845 / 1000000000000) (-5506058721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3051995412839697 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10635608912 / 1000000000000) (-10635608911 / 1000000000000), orderedInterval (-26849114632 / 1000000000000) (-26849114631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3460637513521863 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24590339888 / 1000000000000) (-24590287101 / 1000000000000), orderedInterval (11466582173 / 1000000000000) (11466634961 / 1000000000000)))) (orderedInterval (-3766022067 / 1000000000000) (-3766017677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2885118769177047 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14279566487 / 1000000000000) (-14279566377 / 1000000000000), orderedInterval (26062144109 / 1000000000000) (26062144219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2549089929441987 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9773473874 / 1000000000000) (-9773473873 / 1000000000000), orderedInterval (-30049863846 / 1000000000000) (-30049863845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (738825617104713 / 800000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16692996718 / 1000000000000) (16692996719 / 1000000000000), orderedInterval (20256091175 / 1000000000000) (20256091176 / 1000000000000)))) (orderedInterval (3587465798 / 1000000000000) (3587465869 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks1_2 :
    compactCertificate628.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2043630539173611 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13316388026 / 1000000000000) (13316388124 / 1000000000000), orderedInterval (-32704479356 / 1000000000000) (-32704479258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1732408240645971 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13052202996 / 1000000000000) (13052202997 / 1000000000000), orderedInterval (36034173083 / 1000000000000) (36034173084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1084060638702513 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48400287062 / 1000000000000) (48400287295 / 1000000000000), orderedInterval (-2624500917 / 1000000000000) (-2624500684 / 1000000000000)))) (orderedInterval (3533845881 / 1000000000000) (3533846017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (583011416917071 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59413548240 / 1000000000000) (59413559296 / 1000000000000), orderedInterval (-29148885654 / 1000000000000) (-29148874598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1582989408804213 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25584633361 / 1000000000000) (25584633362 / 1000000000000), orderedInterval (30855841322 / 1000000000000) (30855841323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2161436703794901 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24392026540 / 1000000000000) (24392026541 / 1000000000000), orderedInterval (24126361693 / 1000000000000) (24126361694 / 1000000000000)))) (orderedInterval (-2397829173 / 1000000000000) (-2397829059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (913939361297487 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3511426461 / 1000000000000) (3511426468 / 1000000000000), orderedInterval (-52675924117 / 1000000000000) (-52675924110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3715112763278127 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8927444672 / 1000000000000) (-8927444669 / 1000000000000), orderedInterval (24616565551 / 1000000000000) (24616565553 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2481523152447393 / 4000000000000) 1 (IntervalRat.scale (999 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24471288188 / 1000000000000) (-24471273873 / 1000000000000), orderedInterval (20691729762 / 1000000000000) (20691744078 / 1000000000000)))) (orderedInterval (-8693067691 / 1000000000000) (-8693064161 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks1 :
    compactCertificate628.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate628.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate628_chunkChecks1_0
    compactCertificate628_chunkChecks1_1 compactCertificate628_chunkChecks1_2

theorem compactCertificate628_chunkChecks2_0 :
    compactCertificate628.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (999 / 2) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24901316935 / 1000000000000) (-24901316934 / 1000000000000), orderedInterval (-25557069227 / 1000000000000) (-25557069226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1471717756953099 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37936478519 / 1000000000000) (-37936478518 / 1000000000000), orderedInterval (-17010079546 / 1000000000000) (-17010079545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (475923284249067 / 800000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30644618278 / 1000000000000) (-30644580123 / 1000000000000), orderedInterval (11472565248 / 1000000000000) (11472603403 / 1000000000000)))) (orderedInterval (12631508096 / 1000000000000) (12631511323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (429443570962593 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74800439968 / 1000000000000) (74800439970 / 1000000000000), orderedInterval (17942484584 / 1000000000000) (17942484585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1153545837840621 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6784221665 / 1000000000000) (6784221666 / 1000000000000), orderedInterval (46480179116 / 1000000000000) (46480179117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3132101346360057 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28509584989 / 1000000000000) (-28509582641 / 1000000000000), orderedInterval (-460573161 / 1000000000000) (-460570813 / 1000000000000)))) (orderedInterval (-5027613946 / 1000000000000) (-5027613440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2307091675682241 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15780406368 / 1000000000000) (-15780406096 / 1000000000000), orderedInterval (29249626115 / 1000000000000) (29249626387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3953240909399493 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12305436494 / 1000000000000) (12305436510 / 1000000000000), orderedInterval (-22203658065 / 1000000000000) (-22203658049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2911939361297487 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2346390947 / 1000000000000) (-2346390946 / 1000000000000), orderedInterval (29480257611 / 1000000000000) (29480257612 / 1000000000000)))) (orderedInterval (1601539243 / 1000000000000) (1601539332 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks2_1 :
    compactCertificate628.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4467663819044001 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15484841455 / 1000000000000) (-15484841339 / 1000000000000), orderedInterval (18178330052 / 1000000000000) (18178330168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2579406908573529 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31395597811 / 1000000000000) (-31395595795 / 1000000000000), orderedInterval (1269552525 / 1000000000000) (1269554542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4577202823530861 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23579748758 / 1000000000000) (23579763283 / 1000000000000), orderedInterval (568156408 / 1000000000000) (568170933 / 1000000000000)))) (orderedInterval (-27458512185 / 1000000000000) (-27458500107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4276616616876609 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23774883129 / 1000000000000) (23774982252 / 1000000000000), orderedInterval (-5506157845 / 1000000000000) (-5506058721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3051995412839697 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10635608912 / 1000000000000) (-10635608911 / 1000000000000), orderedInterval (-26849114632 / 1000000000000) (-26849114631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3460637513521863 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24590339888 / 1000000000000) (-24590287101 / 1000000000000), orderedInterval (11466582173 / 1000000000000) (11466634961 / 1000000000000)))) (orderedInterval (3947362140 / 1000000000000) (3947371309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2885118769177047 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14279566487 / 1000000000000) (-14279566377 / 1000000000000), orderedInterval (26062144109 / 1000000000000) (26062144219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2549089929441987 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9773473874 / 1000000000000) (-9773473873 / 1000000000000), orderedInterval (-30049863846 / 1000000000000) (-30049863845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (738825617104713 / 800000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16692996718 / 1000000000000) (16692996719 / 1000000000000), orderedInterval (20256091175 / 1000000000000) (20256091176 / 1000000000000)))) (orderedInterval (-2034819912 / 1000000000000) (-2034819806 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks2_2 :
    compactCertificate628.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2043630539173611 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13316388026 / 1000000000000) (13316388124 / 1000000000000), orderedInterval (-32704479356 / 1000000000000) (-32704479258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1732408240645971 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13052202996 / 1000000000000) (13052202997 / 1000000000000), orderedInterval (36034173083 / 1000000000000) (36034173084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1084060638702513 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48400287062 / 1000000000000) (48400287295 / 1000000000000), orderedInterval (-2624500917 / 1000000000000) (-2624500684 / 1000000000000)))) (orderedInterval (2312024980 / 1000000000000) (2312025109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (583011416917071 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59413548240 / 1000000000000) (59413559296 / 1000000000000), orderedInterval (-29148885654 / 1000000000000) (-29148874598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1582989408804213 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25584633361 / 1000000000000) (25584633362 / 1000000000000), orderedInterval (30855841322 / 1000000000000) (30855841323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2161436703794901 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24392026540 / 1000000000000) (24392026541 / 1000000000000), orderedInterval (24126361693 / 1000000000000) (24126361694 / 1000000000000)))) (orderedInterval (2650278481 / 1000000000000) (2650278553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (913939361297487 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3511426461 / 1000000000000) (3511426468 / 1000000000000), orderedInterval (-52675924117 / 1000000000000) (-52675924110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3715112763278127 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8927444672 / 1000000000000) (-8927444669 / 1000000000000), orderedInterval (24616565551 / 1000000000000) (24616565553 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2481523152447393 / 4000000000000) 2 (IntervalRat.scale (999 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24471288188 / 1000000000000) (-24471273873 / 1000000000000), orderedInterval (20691729762 / 1000000000000) (20691744078 / 1000000000000)))) (orderedInterval (-9582238244 / 1000000000000) (-9582233806 / 1000000000000))) = true
  rfl'

theorem compactCertificate628_chunkChecks2 :
    compactCertificate628.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate628.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate628_chunkChecks2_0
    compactCertificate628_chunkChecks2_1 compactCertificate628_chunkChecks2_2

theorem compactCertificate628_chunkChecks3_0 :
    compactCertificate628.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (999 / 2) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24901316935 / 1000000000000) (-24901316934 / 1000000000000), orderedInterval (-25557069227 / 1000000000000) (-25557069226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1471717756953099 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37936478519 / 1000000000000) (-37936478518 / 1000000000000), orderedInterval (-17010079546 / 1000000000000) (-17010079545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (475923284249067 / 800000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30644618278 / 1000000000000) (-30644580123 / 1000000000000), orderedInterval (11472565248 / 1000000000000) (11472603403 / 1000000000000)))) (orderedInterval (9030595218 / 1000000000000) (9030599059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (429443570962593 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74800439968 / 1000000000000) (74800439970 / 1000000000000), orderedInterval (17942484584 / 1000000000000) (17942484585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1153545837840621 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6784221665 / 1000000000000) (6784221666 / 1000000000000), orderedInterval (46480179116 / 1000000000000) (46480179117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3132101346360057 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28509584989 / 1000000000000) (-28509582641 / 1000000000000), orderedInterval (-460573161 / 1000000000000) (-460570813 / 1000000000000)))) (orderedInterval (-440731822 / 1000000000000) (-440731037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2307091675682241 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15780406368 / 1000000000000) (-15780406096 / 1000000000000), orderedInterval (29249626115 / 1000000000000) (29249626387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3953240909399493 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12305436494 / 1000000000000) (12305436510 / 1000000000000), orderedInterval (-22203658065 / 1000000000000) (-22203658049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2911939361297487 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2346390947 / 1000000000000) (-2346390946 / 1000000000000), orderedInterval (29480257611 / 1000000000000) (29480257612 / 1000000000000)))) (orderedInterval (-7513623802 / 1000000000000) (-7513623641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate628_chunkChecks3_1 :
    compactCertificate628.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4467663819044001 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15484841455 / 1000000000000) (-15484841339 / 1000000000000), orderedInterval (18178330052 / 1000000000000) (18178330168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2579406908573529 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31395597811 / 1000000000000) (-31395595795 / 1000000000000), orderedInterval (1269552525 / 1000000000000) (1269554542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4577202823530861 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23579748758 / 1000000000000) (23579763283 / 1000000000000), orderedInterval (568156408 / 1000000000000) (568170933 / 1000000000000)))) (orderedInterval (34994742146 / 1000000000000) (34994769472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4276616616876609 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23774883129 / 1000000000000) (23774982252 / 1000000000000), orderedInterval (-5506157845 / 1000000000000) (-5506058721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3051995412839697 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10635608912 / 1000000000000) (-10635608911 / 1000000000000), orderedInterval (-26849114632 / 1000000000000) (-26849114631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3460637513521863 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24590339888 / 1000000000000) (-24590287101 / 1000000000000), orderedInterval (11466582173 / 1000000000000) (11466634961 / 1000000000000)))) (orderedInterval (8368120354 / 1000000000000) (8368139580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2885118769177047 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14279566487 / 1000000000000) (-14279566377 / 1000000000000), orderedInterval (26062144109 / 1000000000000) (26062144219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2549089929441987 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9773473874 / 1000000000000) (-9773473873 / 1000000000000), orderedInterval (-30049863846 / 1000000000000) (-30049863845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (738825617104713 / 800000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16692996718 / 1000000000000) (16692996719 / 1000000000000), orderedInterval (20256091175 / 1000000000000) (20256091176 / 1000000000000)))) (orderedInterval (-7751270131 / 1000000000000) (-7751269968 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate628_chunkChecks3_2 :
    compactCertificate628.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2043630539173611 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13316388026 / 1000000000000) (13316388124 / 1000000000000), orderedInterval (-32704479356 / 1000000000000) (-32704479258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1732408240645971 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13052202996 / 1000000000000) (13052202997 / 1000000000000), orderedInterval (36034173083 / 1000000000000) (36034173084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1084060638702513 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48400287062 / 1000000000000) (48400287295 / 1000000000000), orderedInterval (-2624500917 / 1000000000000) (-2624500684 / 1000000000000)))) (orderedInterval (-4257165972 / 1000000000000) (-4257165847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (583011416917071 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59413548240 / 1000000000000) (59413559296 / 1000000000000), orderedInterval (-29148885654 / 1000000000000) (-29148874598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1582989408804213 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25584633361 / 1000000000000) (25584633362 / 1000000000000), orderedInterval (30855841322 / 1000000000000) (30855841323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2161436703794901 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24392026540 / 1000000000000) (24392026541 / 1000000000000), orderedInterval (24126361693 / 1000000000000) (24126361694 / 1000000000000)))) (orderedInterval (2670351776 / 1000000000000) (2670351836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (913939361297487 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3511426461 / 1000000000000) (3511426468 / 1000000000000), orderedInterval (-52675924117 / 1000000000000) (-52675924110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3715112763278127 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8927444672 / 1000000000000) (-8927444669 / 1000000000000), orderedInterval (24616565551 / 1000000000000) (24616565553 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2481523152447393 / 4000000000000) 3 (IntervalRat.scale (999 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24471288188 / 1000000000000) (-24471273873 / 1000000000000), orderedInterval (20691729762 / 1000000000000) (20691744078 / 1000000000000)))) (orderedInterval (20369825469 / 1000000000000) (20369831067 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate628_chunkChecks3 :
    compactCertificate628.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate628.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate628_chunkChecks3_0
    compactCertificate628_chunkChecks3_1 compactCertificate628_chunkChecks3_2

theorem compactCertificate628_chunkChecks4_0 :
    compactCertificate628.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (999 / 2) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24901316935 / 1000000000000) (-24901316934 / 1000000000000), orderedInterval (-25557069227 / 1000000000000) (-25557069226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1471717756953099 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37936478519 / 1000000000000) (-37936478518 / 1000000000000), orderedInterval (-17010079546 / 1000000000000) (-17010079545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (475923284249067 / 800000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30644618278 / 1000000000000) (-30644580123 / 1000000000000), orderedInterval (11472565248 / 1000000000000) (11472603403 / 1000000000000)))) (orderedInterval (-13628432434 / 1000000000000) (-13628427852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (429443570962593 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (74800439968 / 1000000000000) (74800439970 / 1000000000000), orderedInterval (17942484584 / 1000000000000) (17942484585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1153545837840621 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6784221665 / 1000000000000) (6784221666 / 1000000000000), orderedInterval (46480179116 / 1000000000000) (46480179117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3132101346360057 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28509584989 / 1000000000000) (-28509582641 / 1000000000000), orderedInterval (-460573161 / 1000000000000) (-460570813 / 1000000000000)))) (orderedInterval (12266888326 / 1000000000000) (12266889555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2307091675682241 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-15780406368 / 1000000000000) (-15780406096 / 1000000000000), orderedInterval (29249626115 / 1000000000000) (29249626387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3953240909399493 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12305436494 / 1000000000000) (12305436510 / 1000000000000), orderedInterval (-22203658065 / 1000000000000) (-22203658049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2911939361297487 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2346390947 / 1000000000000) (-2346390946 / 1000000000000), orderedInterval (29480257611 / 1000000000000) (29480257612 / 1000000000000)))) (orderedInterval (-6042759325 / 1000000000000) (-6042759026 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate628_chunkChecks4_1 :
    compactCertificate628.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4467663819044001 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15484841455 / 1000000000000) (-15484841339 / 1000000000000), orderedInterval (18178330052 / 1000000000000) (18178330168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2579406908573529 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31395597811 / 1000000000000) (-31395595795 / 1000000000000), orderedInterval (1269552525 / 1000000000000) (1269554542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4577202823530861 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23579748758 / 1000000000000) (23579763283 / 1000000000000), orderedInterval (568156408 / 1000000000000) (568170933 / 1000000000000)))) (orderedInterval (154510685300 / 1000000000000) (154510747482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4276616616876609 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23774883129 / 1000000000000) (23774982252 / 1000000000000), orderedInterval (-5506157845 / 1000000000000) (-5506058721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3051995412839697 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10635608912 / 1000000000000) (-10635608911 / 1000000000000), orderedInterval (-26849114632 / 1000000000000) (-26849114631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3460637513521863 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24590339888 / 1000000000000) (-24590287101 / 1000000000000), orderedInterval (11466582173 / 1000000000000) (11466634961 / 1000000000000)))) (orderedInterval (-13398481185 / 1000000000000) (-13398440673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2885118769177047 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14279566487 / 1000000000000) (-14279566377 / 1000000000000), orderedInterval (26062144109 / 1000000000000) (26062144219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2549089929441987 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9773473874 / 1000000000000) (-9773473873 / 1000000000000), orderedInterval (-30049863846 / 1000000000000) (-30049863845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (738825617104713 / 800000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16692996718 / 1000000000000) (16692996719 / 1000000000000), orderedInterval (20256091175 / 1000000000000) (20256091176 / 1000000000000)))) (orderedInterval (5790619281 / 1000000000000) (5790619539 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate628_chunkChecks4_2 :
    compactCertificate628.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2043630539173611 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13316388026 / 1000000000000) (13316388124 / 1000000000000), orderedInterval (-32704479356 / 1000000000000) (-32704479258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1732408240645971 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13052202996 / 1000000000000) (13052202997 / 1000000000000), orderedInterval (36034173083 / 1000000000000) (36034173084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1084060638702513 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48400287062 / 1000000000000) (48400287295 / 1000000000000), orderedInterval (-2624500917 / 1000000000000) (-2624500684 / 1000000000000)))) (orderedInterval (-2594413795 / 1000000000000) (-2594413671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (583011416917071 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59413548240 / 1000000000000) (59413559296 / 1000000000000), orderedInterval (-29148885654 / 1000000000000) (-29148874598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1582989408804213 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25584633361 / 1000000000000) (25584633362 / 1000000000000), orderedInterval (30855841322 / 1000000000000) (30855841323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2161436703794901 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24392026540 / 1000000000000) (24392026541 / 1000000000000), orderedInterval (24126361693 / 1000000000000) (24126361694 / 1000000000000)))) (orderedInterval (-2807610577 / 1000000000000) (-2807610517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (913939361297487 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3511426461 / 1000000000000) (3511426468 / 1000000000000), orderedInterval (-52675924117 / 1000000000000) (-52675924110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3715112763278127 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8927444672 / 1000000000000) (-8927444669 / 1000000000000), orderedInterval (24616565551 / 1000000000000) (24616565553 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2481523152447393 / 4000000000000) 4 (IntervalRat.scale (999 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24471288188 / 1000000000000) (-24471273873 / 1000000000000), orderedInterval (20691729762 / 1000000000000) (20691744078 / 1000000000000)))) (orderedInterval (19531795412 / 1000000000000) (19531802537 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate628_chunkChecks4 :
    compactCertificate628.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate628.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate628_chunkChecks4_0
    compactCertificate628_chunkChecks4_1 compactCertificate628_chunkChecks4_2

theorem compactCertificate628_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate628.chunkCheck r b = true :=
  compactCertificate628.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate628_chunkChecks0
    · exact compactCertificate628_chunkChecks1
    · exact compactCertificate628_chunkChecks2
    · exact compactCertificate628_chunkChecks3
    · exact compactCertificate628_chunkChecks4)

theorem compactCertificate628_coefficient0 :
    compactCertificate628.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate628_coefficient1 :
    compactCertificate628.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate628_coefficient2 :
    compactCertificate628.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate628_coefficient3 :
    compactCertificate628.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate628_coefficient4 :
    compactCertificate628.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate628_coefficients : ∀ r : Fin 5,
    compactCertificate628.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate628_coefficient0
  · exact compactCertificate628_coefficient1
  · exact compactCertificate628_coefficient2
  · exact compactCertificate628_coefficient3
  · exact compactCertificate628_coefficient4

theorem compactCertificate628_lower : (1 : ℚ) ≤ compactCertificate628.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate628, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate628_proves {t : ℝ} (ht : t ∈ compactCertificate628.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate628.proves compactCertificate628_states compactCertificate628_chunks
    compactCertificate628_coefficients compactCertificate628_lower ht

end Erdos232
