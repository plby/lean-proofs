/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate602 : CompactCertificate where
  left := 473
  right := 474
  center := 947 / 2
  grid := fun i =>
    match i.val with
    | 0 => 151
    | 1 => 111
    | 2 => 180
    | 3 => 32
    | 4 => 87
    | 5 => 236
    | 6 => 174
    | 7 => 298
    | 8 => 220
    | 9 => 337
    | 10 => 195
    | 11 => 345
    | 12 => 323
    | 13 => 230
    | 14 => 261
    | 15 => 218
    | 16 => 192
    | 17 => 279
    | 18 => 154
    | 19 => 131
    | 20 => 82
    | 21 => 44
    | 22 => 119
    | 23 => 163
    | 24 => 69
    | 25 => 280
    | _ => 187
  point := fun i =>
    match i.val with
    | 0 => 947 / 2
    | 1 => 1395111827662247 / 4000000000000
    | 2 => 451150500684551 / 800000000000
    | 3 => 407090151853429 / 4000000000000
    | 4 => 1093501409844913 / 4000000000000
    | 5 => 2969069044047021 / 4000000000000
    | 6 => 2187002819690773 / 4000000000000
    | 7 => 3747466607809129 / 4000000000000
    | 8 => 2760366942090811 / 4000000000000
    | 9 => 4235112749384053 / 4000000000000
    | 10 => 2445143485905037 / 4000000000000
    | 11 => 4338950023907633 / 4000000000000
    | 12 => 4054009946128277 / 4000000000000
    | 13 => 2893132788747941 / 4000000000000
    | 14 => 3280504229534739 / 4000000000000
    | 15 => 2734942416827491 / 4000000000000
    | 16 => 2416404567749311 / 4000000000000
    | 17 => 700368227625789 / 800000000000
    | 18 => 1937255375973383 / 4000000000000
    | 19 => 1642232836728463 / 4000000000000
    | 20 => 1027633057909189 / 4000000000000
    | 21 => 552664476296763 / 4000000000000
    | 22 => 1500591561699289 / 4000000000000
    | 23 => 2048929487981753 / 4000000000000
    | 24 => 866366942090811 / 4000000000000
    | 25 => 3521733520344731 / 4000000000000
    | _ => 2352354780147829 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (3491177877 / 1000000000000) (3491177879 / 1000000000000), orderedInterval (-36504513243 / 1000000000000) (-36504513241 / 1000000000000))
    | 1 => (orderedInterval (-31990182328 / 1000000000000) (-31990182327 / 1000000000000), orderedInterval (-28272238611 / 1000000000000) (-28272238610 / 1000000000000))
    | 2 => (orderedInterval (-23229031125 / 1000000000000) (-23229024518 / 1000000000000), orderedInterval (24295982589 / 1000000000000) (24295989197 / 1000000000000))
    | 3 => (orderedInterval (71045403964 / 1000000000000) (71045412992 / 1000000000000), orderedInterval (-35102789403 / 1000000000000) (-35102780376 / 1000000000000))
    | 4 => (orderedInterval (-35989968284 / 1000000000000) (-35989968283 / 1000000000000), orderedInterval (-32081655177 / 1000000000000) (-32081655176 / 1000000000000))
    | 5 => (orderedInterval (29222553915 / 1000000000000) (29222558517 / 1000000000000), orderedInterval (-1946139056 / 1000000000000) (-1946134453 / 1000000000000))
    | 6 => (orderedInterval (26702869926 / 1000000000000) (26702869927 / 1000000000000), orderedInterval (21220014878 / 1000000000000) (21220014879 / 1000000000000))
    | 7 => (orderedInterval (25899908349 / 1000000000000) (25899910253 / 1000000000000), orderedInterval (2938253254 / 1000000000000) (2938255157 / 1000000000000))
    | 8 => (orderedInterval (-8201806616 / 1000000000000) (-8201806611 / 1000000000000), orderedInterval (29250519442 / 1000000000000) (29250519446 / 1000000000000))
    | 9 => (orderedInterval (-18369316016 / 1000000000000) (-18369316015 / 1000000000000), orderedInterval (-16234661610 / 1000000000000) (-16234661609 / 1000000000000))
    | 10 => (orderedInterval (16578109967 / 1000000000000) (16578110354 / 1000000000000), orderedInterval (-27701284032 / 1000000000000) (-27701283645 / 1000000000000))
    | 11 => (orderedInterval (-24098577471 / 1000000000000) (-24098541522 / 1000000000000), orderedInterval (2490539293 / 1000000000000) (2490575242 / 1000000000000))
    | 12 => (orderedInterval (10826098333 / 1000000000000) (10826098338 / 1000000000000), orderedInterval (-22609189846 / 1000000000000) (-22609189840 / 1000000000000))
    | 13 => (orderedInterval (29597880626 / 1000000000000) (29597881535 / 1000000000000), orderedInterval (2015646620 / 1000000000000) (2015647529 / 1000000000000))
    | 14 => (orderedInterval (-22753457006 / 1000000000000) (-22753457005 / 1000000000000), orderedInterval (-16064883970 / 1000000000000) (-16064883969 / 1000000000000))
    | 15 => (orderedInterval (-10359243757 / 1000000000000) (-10359243743 / 1000000000000), orderedInterval (28709088122 / 1000000000000) (28709088137 / 1000000000000))
    | 16 => (orderedInterval (32189874775 / 1000000000000) (32189879088 / 1000000000000), orderedInterval (-4226793528 / 1000000000000) (-4226789215 / 1000000000000))
    | 17 => (orderedInterval (6901513433 / 1000000000000) (6901513435 / 1000000000000), orderedInterval (-26072162581 / 1000000000000) (-26072162579 / 1000000000000))
    | 18 => (orderedInterval (34872853608 / 1000000000000) (34872853617 / 1000000000000), orderedInterval (9881721038 / 1000000000000) (9881721047 / 1000000000000))
    | 19 => (orderedInterval (8028951663 / 1000000000000) (8028951677 / 1000000000000), orderedInterval (-38560484879 / 1000000000000) (-38560484864 / 1000000000000))
    | 20 => (orderedInterval (4106046601 / 1000000000000) (4106046602 / 1000000000000), orderedInterval (49601980185 / 1000000000000) (49601980186 / 1000000000000))
    | 21 => (orderedInterval (44785958418 / 1000000000000) (44785958419 / 1000000000000), orderedInterval (50846380396 / 1000000000000) (50846380397 / 1000000000000))
    | 22 => (orderedInterval (-35899169000 / 1000000000000) (-35899112743 / 1000000000000), orderedInterval (20252626996 / 1000000000000) (20252683253 / 1000000000000))
    | 23 => (orderedInterval (-28426290675 / 1000000000000) (-28426290674 / 1000000000000), orderedInterval (-20823625461 / 1000000000000) (-20823625460 / 1000000000000))
    | 24 => (orderedInterval (-30909505270 / 1000000000000) (-30909505269 / 1000000000000), orderedInterval (-44469266078 / 1000000000000) (-44469266077 / 1000000000000))
    | 25 => (orderedInterval (26890009436 / 1000000000000) (26890014346 / 1000000000000), orderedInterval (-66282186 / 1000000000000) (-66277275 / 1000000000000))
    | _ => (orderedInterval (-32400671759 / 1000000000000) (-32400671665 / 1000000000000), orderedInterval (-5692549025 / 1000000000000) (-5692548931 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-277411788 / 1000000000000) (-277411366 / 1000000000000)
      | 1 => orderedInterval (-4162270163 / 1000000000000) (-4162269681 / 1000000000000)
      | 2 => orderedInterval (-997078355 / 1000000000000) (-997078269 / 1000000000000)
      | 3 => orderedInterval (1066552322 / 1000000000000) (1066557649 / 1000000000000)
      | 4 => orderedInterval (2718561505 / 1000000000000) (2718561648 / 1000000000000)
      | 5 => orderedInterval (-1785038960 / 1000000000000) (-1785038667 / 1000000000000)
      | 6 => orderedInterval (-5896670636 / 1000000000000) (-5896670514 / 1000000000000)
      | 7 => orderedInterval (2166019022 / 1000000000000) (2166020355 / 1000000000000)
      | _ => orderedInterval (3703997844 / 1000000000000) (3703998393 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12965135069 / 1000000000000) (-12965134569 / 1000000000000)
      | 1 => orderedInterval (-377546902 / 1000000000000) (-377546303 / 1000000000000)
      | 2 => orderedInterval (850979476 / 1000000000000) (850979639 / 1000000000000)
      | 3 => orderedInterval (4611786157 / 1000000000000) (4611798291 / 1000000000000)
      | 4 => orderedInterval (1305623562 / 1000000000000) (1305623785 / 1000000000000)
      | 5 => orderedInterval (-446920034 / 1000000000000) (-446919653 / 1000000000000)
      | 6 => orderedInterval (1152454583 / 1000000000000) (1152454695 / 1000000000000)
      | 7 => orderedInterval (1088447805 / 1000000000000) (1088448868 / 1000000000000)
      | _ => orderedInterval (1213957421 / 1000000000000) (1213958370 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (738871277 / 1000000000000) (738871872 / 1000000000000)
      | 1 => orderedInterval (5579535423 / 1000000000000) (5579536322 / 1000000000000)
      | 2 => orderedInterval (3546651674 / 1000000000000) (3546651987 / 1000000000000)
      | 3 => orderedInterval (-397961065 / 1000000000000) (-397933338 / 1000000000000)
      | 4 => orderedInterval (-5983435787 / 1000000000000) (-5983435434 / 1000000000000)
      | 5 => orderedInterval (2644766282 / 1000000000000) (2644766783 / 1000000000000)
      | 6 => orderedInterval (6133367184 / 1000000000000) (6133367291 / 1000000000000)
      | 7 => orderedInterval (-2992672940 / 1000000000000) (-2992672086 / 1000000000000)
      | _ => orderedInterval (-1773280901 / 1000000000000) (-1773279218 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (12164163476 / 1000000000000) (12164164182 / 1000000000000)
      | 1 => orderedInterval (-323107168 / 1000000000000) (-323105771 / 1000000000000)
      | 2 => orderedInterval (-1493936042 / 1000000000000) (-1493935437 / 1000000000000)
      | 3 => orderedInterval (-32091716213 / 1000000000000) (-32091652824 / 1000000000000)
      | 4 => orderedInterval (-5091833692 / 1000000000000) (-5091833127 / 1000000000000)
      | 5 => orderedInterval (2713124792 / 1000000000000) (2713125456 / 1000000000000)
      | 6 => orderedInterval (-2847924 / 1000000000000) (-2847820 / 1000000000000)
      | 7 => orderedInterval (-1762281688 / 1000000000000) (-1762280999 / 1000000000000)
      | _ => orderedInterval (-2051579462 / 1000000000000) (-2051576436 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1498030456 / 1000000000000) (-1498029614 / 1000000000000)
      | 1 => orderedInterval (-12691700342 / 1000000000000) (-12691698154 / 1000000000000)
      | 2 => orderedInterval (-13131351683 / 1000000000000) (-13131350504 / 1000000000000)
      | 3 => orderedInterval (-9209545370 / 1000000000000) (-9209400213 / 1000000000000)
      | 4 => orderedInterval (12193585815 / 1000000000000) (12193586732 / 1000000000000)
      | 5 => orderedInterval (-3347209651 / 1000000000000) (-3347208755 / 1000000000000)
      | 6 => orderedInterval (-6348229801 / 1000000000000) (-6348229699 / 1000000000000)
      | 7 => orderedInterval (3306064202 / 1000000000000) (3306064763 / 1000000000000)
      | _ => orderedInterval (-11699411533 / 1000000000000) (-11699406029 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3463339209 / 1000000000000) (-3463330452 / 1000000000000)
    | 1 => orderedInterval (-3566353001 / 1000000000000) (-3566336877 / 1000000000000)
    | 2 => orderedInterval (7495841147 / 1000000000000) (7495874179 / 1000000000000)
    | 3 => orderedInterval (-27940013921 / 1000000000000) (-27939942776 / 1000000000000)
    | _ => orderedInterval (-42425828819 / 1000000000000) (-42425671473 / 1000000000000)

theorem compactCertificate602_stateChecks0 :
    compactCertificate602.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (947 / 2)) (orderedInterval (3491177877 / 1000000000000) (3491177879 / 1000000000000), orderedInterval (-36504513243 / 1000000000000) (-36504513241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1395111827662247 / 4000000000000)) (orderedInterval (-31990182328 / 1000000000000) (-31990182327 / 1000000000000), orderedInterval (-28272238611 / 1000000000000) (-28272238610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (451150500684551 / 800000000000)) (orderedInterval (-23229031125 / 1000000000000) (-23229024518 / 1000000000000), orderedInterval (24295982589 / 1000000000000) (24295989197 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_stateChecks1 :
    compactCertificate602.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (407090151853429 / 4000000000000)) (orderedInterval (71045403964 / 1000000000000) (71045412992 / 1000000000000), orderedInterval (-35102789403 / 1000000000000) (-35102780376 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1093501409844913 / 4000000000000)) (orderedInterval (-35989968284 / 1000000000000) (-35989968283 / 1000000000000), orderedInterval (-32081655177 / 1000000000000) (-32081655176 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2969069044047021 / 4000000000000)) (orderedInterval (29222553915 / 1000000000000) (29222558517 / 1000000000000), orderedInterval (-1946139056 / 1000000000000) (-1946134453 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_stateChecks2 :
    compactCertificate602.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2187002819690773 / 4000000000000)) (orderedInterval (26702869926 / 1000000000000) (26702869927 / 1000000000000), orderedInterval (21220014878 / 1000000000000) (21220014879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 298 12 (3747466607809129 / 4000000000000)) (orderedInterval (25899908349 / 1000000000000) (25899910253 / 1000000000000), orderedInterval (2938253254 / 1000000000000) (2938255157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2760366942090811 / 4000000000000)) (orderedInterval (-8201806616 / 1000000000000) (-8201806611 / 1000000000000), orderedInterval (29250519442 / 1000000000000) (29250519446 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_stateChecks3 :
    compactCertificate602.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 337 12 (4235112749384053 / 4000000000000)) (orderedInterval (-18369316016 / 1000000000000) (-18369316015 / 1000000000000), orderedInterval (-16234661610 / 1000000000000) (-16234661609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2445143485905037 / 4000000000000)) (orderedInterval (16578109967 / 1000000000000) (16578110354 / 1000000000000), orderedInterval (-27701284032 / 1000000000000) (-27701283645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 345 12 (4338950023907633 / 4000000000000)) (orderedInterval (-24098577471 / 1000000000000) (-24098541522 / 1000000000000), orderedInterval (2490539293 / 1000000000000) (2490575242 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_stateChecks4 :
    compactCertificate602.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 323 12 (4054009946128277 / 4000000000000)) (orderedInterval (10826098333 / 1000000000000) (10826098338 / 1000000000000), orderedInterval (-22609189846 / 1000000000000) (-22609189840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2893132788747941 / 4000000000000)) (orderedInterval (29597880626 / 1000000000000) (29597881535 / 1000000000000), orderedInterval (2015646620 / 1000000000000) (2015647529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (3280504229534739 / 4000000000000)) (orderedInterval (-22753457006 / 1000000000000) (-22753457005 / 1000000000000), orderedInterval (-16064883970 / 1000000000000) (-16064883969 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_stateChecks5 :
    compactCertificate602.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2734942416827491 / 4000000000000)) (orderedInterval (-10359243757 / 1000000000000) (-10359243743 / 1000000000000), orderedInterval (28709088122 / 1000000000000) (28709088137 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2416404567749311 / 4000000000000)) (orderedInterval (32189874775 / 1000000000000) (32189879088 / 1000000000000), orderedInterval (-4226793528 / 1000000000000) (-4226789215 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (700368227625789 / 800000000000)) (orderedInterval (6901513433 / 1000000000000) (6901513435 / 1000000000000), orderedInterval (-26072162581 / 1000000000000) (-26072162579 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_stateChecks6 :
    compactCertificate602.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1937255375973383 / 4000000000000)) (orderedInterval (34872853608 / 1000000000000) (34872853617 / 1000000000000), orderedInterval (9881721038 / 1000000000000) (9881721047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1642232836728463 / 4000000000000)) (orderedInterval (8028951663 / 1000000000000) (8028951677 / 1000000000000), orderedInterval (-38560484879 / 1000000000000) (-38560484864 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1027633057909189 / 4000000000000)) (orderedInterval (4106046601 / 1000000000000) (4106046602 / 1000000000000), orderedInterval (49601980185 / 1000000000000) (49601980186 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_stateChecks7 :
    compactCertificate602.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (552664476296763 / 4000000000000)) (orderedInterval (44785958418 / 1000000000000) (44785958419 / 1000000000000), orderedInterval (50846380396 / 1000000000000) (50846380397 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1500591561699289 / 4000000000000)) (orderedInterval (-35899169000 / 1000000000000) (-35899112743 / 1000000000000), orderedInterval (20252626996 / 1000000000000) (20252683253 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2048929487981753 / 4000000000000)) (orderedInterval (-28426290675 / 1000000000000) (-28426290674 / 1000000000000), orderedInterval (-20823625461 / 1000000000000) (-20823625460 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_stateChecks8 :
    compactCertificate602.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (866366942090811 / 4000000000000)) (orderedInterval (-30909505270 / 1000000000000) (-30909505269 / 1000000000000), orderedInterval (-44469266078 / 1000000000000) (-44469266077 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 280 12 (3521733520344731 / 4000000000000)) (orderedInterval (26890009436 / 1000000000000) (26890014346 / 1000000000000), orderedInterval (-66282186 / 1000000000000) (-66277275 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2352354780147829 / 4000000000000)) (orderedInterval (-32400671759 / 1000000000000) (-32400671665 / 1000000000000), orderedInterval (-5692549025 / 1000000000000) (-5692548931 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_states : ∀ j,
    BesselStateValid (compactCertificate602.point j) (compactCertificate602.state j) :=
  compactCertificate602.statesValid_of_checks3 compactCertificate602_stateChecks0
    compactCertificate602_stateChecks1 compactCertificate602_stateChecks2
    compactCertificate602_stateChecks3 compactCertificate602_stateChecks4
    compactCertificate602_stateChecks5 compactCertificate602_stateChecks6
    compactCertificate602_stateChecks7 compactCertificate602_stateChecks8

theorem compactCertificate602_chunkChecks0_0 :
    compactCertificate602.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (947 / 2) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3491177877 / 1000000000000) (3491177879 / 1000000000000), orderedInterval (-36504513243 / 1000000000000) (-36504513241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1395111827662247 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31990182328 / 1000000000000) (-31990182327 / 1000000000000), orderedInterval (-28272238611 / 1000000000000) (-28272238610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (451150500684551 / 800000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23229031125 / 1000000000000) (-23229024518 / 1000000000000), orderedInterval (24295982589 / 1000000000000) (24295989197 / 1000000000000)))) (orderedInterval (-277411788 / 1000000000000) (-277411366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (407090151853429 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71045403964 / 1000000000000) (71045412992 / 1000000000000), orderedInterval (-35102789403 / 1000000000000) (-35102780376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1093501409844913 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-35989968284 / 1000000000000) (-35989968283 / 1000000000000), orderedInterval (-32081655177 / 1000000000000) (-32081655176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2969069044047021 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29222553915 / 1000000000000) (29222558517 / 1000000000000), orderedInterval (-1946139056 / 1000000000000) (-1946134453 / 1000000000000)))) (orderedInterval (-4162270163 / 1000000000000) (-4162269681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2187002819690773 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26702869926 / 1000000000000) (26702869927 / 1000000000000), orderedInterval (21220014878 / 1000000000000) (21220014879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3747466607809129 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25899908349 / 1000000000000) (25899910253 / 1000000000000), orderedInterval (2938253254 / 1000000000000) (2938255157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2760366942090811 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8201806616 / 1000000000000) (-8201806611 / 1000000000000), orderedInterval (29250519442 / 1000000000000) (29250519446 / 1000000000000)))) (orderedInterval (-997078355 / 1000000000000) (-997078269 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks0_1 :
    compactCertificate602.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4235112749384053 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18369316016 / 1000000000000) (-18369316015 / 1000000000000), orderedInterval (-16234661610 / 1000000000000) (-16234661609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2445143485905037 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16578109967 / 1000000000000) (16578110354 / 1000000000000), orderedInterval (-27701284032 / 1000000000000) (-27701283645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4338950023907633 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24098577471 / 1000000000000) (-24098541522 / 1000000000000), orderedInterval (2490539293 / 1000000000000) (2490575242 / 1000000000000)))) (orderedInterval (1066552322 / 1000000000000) (1066557649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4054009946128277 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10826098333 / 1000000000000) (10826098338 / 1000000000000), orderedInterval (-22609189846 / 1000000000000) (-22609189840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2893132788747941 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29597880626 / 1000000000000) (29597881535 / 1000000000000), orderedInterval (2015646620 / 1000000000000) (2015647529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3280504229534739 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22753457006 / 1000000000000) (-22753457005 / 1000000000000), orderedInterval (-16064883970 / 1000000000000) (-16064883969 / 1000000000000)))) (orderedInterval (2718561505 / 1000000000000) (2718561648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2734942416827491 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10359243757 / 1000000000000) (-10359243743 / 1000000000000), orderedInterval (28709088122 / 1000000000000) (28709088137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2416404567749311 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32189874775 / 1000000000000) (32189879088 / 1000000000000), orderedInterval (-4226793528 / 1000000000000) (-4226789215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (700368227625789 / 800000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6901513433 / 1000000000000) (6901513435 / 1000000000000), orderedInterval (-26072162581 / 1000000000000) (-26072162579 / 1000000000000)))) (orderedInterval (-1785038960 / 1000000000000) (-1785038667 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks0_2 :
    compactCertificate602.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1937255375973383 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34872853608 / 1000000000000) (34872853617 / 1000000000000), orderedInterval (9881721038 / 1000000000000) (9881721047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1642232836728463 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8028951663 / 1000000000000) (8028951677 / 1000000000000), orderedInterval (-38560484879 / 1000000000000) (-38560484864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1027633057909189 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4106046601 / 1000000000000) (4106046602 / 1000000000000), orderedInterval (49601980185 / 1000000000000) (49601980186 / 1000000000000)))) (orderedInterval (-5896670636 / 1000000000000) (-5896670514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (552664476296763 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44785958418 / 1000000000000) (44785958419 / 1000000000000), orderedInterval (50846380396 / 1000000000000) (50846380397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1500591561699289 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35899169000 / 1000000000000) (-35899112743 / 1000000000000), orderedInterval (20252626996 / 1000000000000) (20252683253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2048929487981753 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28426290675 / 1000000000000) (-28426290674 / 1000000000000), orderedInterval (-20823625461 / 1000000000000) (-20823625460 / 1000000000000)))) (orderedInterval (2166019022 / 1000000000000) (2166020355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (866366942090811 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30909505270 / 1000000000000) (-30909505269 / 1000000000000), orderedInterval (-44469266078 / 1000000000000) (-44469266077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3521733520344731 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26890009436 / 1000000000000) (26890014346 / 1000000000000), orderedInterval (-66282186 / 1000000000000) (-66277275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2352354780147829 / 4000000000000) 0 (IntervalRat.scale (947 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32400671759 / 1000000000000) (-32400671665 / 1000000000000), orderedInterval (-5692549025 / 1000000000000) (-5692548931 / 1000000000000)))) (orderedInterval (3703997844 / 1000000000000) (3703998393 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks0 :
    compactCertificate602.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate602.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate602_chunkChecks0_0
    compactCertificate602_chunkChecks0_1 compactCertificate602_chunkChecks0_2

theorem compactCertificate602_chunkChecks1_0 :
    compactCertificate602.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (947 / 2) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3491177877 / 1000000000000) (3491177879 / 1000000000000), orderedInterval (-36504513243 / 1000000000000) (-36504513241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1395111827662247 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31990182328 / 1000000000000) (-31990182327 / 1000000000000), orderedInterval (-28272238611 / 1000000000000) (-28272238610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (451150500684551 / 800000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23229031125 / 1000000000000) (-23229024518 / 1000000000000), orderedInterval (24295982589 / 1000000000000) (24295989197 / 1000000000000)))) (orderedInterval (-12965135069 / 1000000000000) (-12965134569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (407090151853429 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71045403964 / 1000000000000) (71045412992 / 1000000000000), orderedInterval (-35102789403 / 1000000000000) (-35102780376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1093501409844913 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-35989968284 / 1000000000000) (-35989968283 / 1000000000000), orderedInterval (-32081655177 / 1000000000000) (-32081655176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2969069044047021 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29222553915 / 1000000000000) (29222558517 / 1000000000000), orderedInterval (-1946139056 / 1000000000000) (-1946134453 / 1000000000000)))) (orderedInterval (-377546902 / 1000000000000) (-377546303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2187002819690773 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26702869926 / 1000000000000) (26702869927 / 1000000000000), orderedInterval (21220014878 / 1000000000000) (21220014879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3747466607809129 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25899908349 / 1000000000000) (25899910253 / 1000000000000), orderedInterval (2938253254 / 1000000000000) (2938255157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2760366942090811 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8201806616 / 1000000000000) (-8201806611 / 1000000000000), orderedInterval (29250519442 / 1000000000000) (29250519446 / 1000000000000)))) (orderedInterval (850979476 / 1000000000000) (850979639 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks1_1 :
    compactCertificate602.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4235112749384053 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18369316016 / 1000000000000) (-18369316015 / 1000000000000), orderedInterval (-16234661610 / 1000000000000) (-16234661609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2445143485905037 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16578109967 / 1000000000000) (16578110354 / 1000000000000), orderedInterval (-27701284032 / 1000000000000) (-27701283645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4338950023907633 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24098577471 / 1000000000000) (-24098541522 / 1000000000000), orderedInterval (2490539293 / 1000000000000) (2490575242 / 1000000000000)))) (orderedInterval (4611786157 / 1000000000000) (4611798291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4054009946128277 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10826098333 / 1000000000000) (10826098338 / 1000000000000), orderedInterval (-22609189846 / 1000000000000) (-22609189840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2893132788747941 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29597880626 / 1000000000000) (29597881535 / 1000000000000), orderedInterval (2015646620 / 1000000000000) (2015647529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3280504229534739 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22753457006 / 1000000000000) (-22753457005 / 1000000000000), orderedInterval (-16064883970 / 1000000000000) (-16064883969 / 1000000000000)))) (orderedInterval (1305623562 / 1000000000000) (1305623785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2734942416827491 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10359243757 / 1000000000000) (-10359243743 / 1000000000000), orderedInterval (28709088122 / 1000000000000) (28709088137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2416404567749311 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32189874775 / 1000000000000) (32189879088 / 1000000000000), orderedInterval (-4226793528 / 1000000000000) (-4226789215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (700368227625789 / 800000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6901513433 / 1000000000000) (6901513435 / 1000000000000), orderedInterval (-26072162581 / 1000000000000) (-26072162579 / 1000000000000)))) (orderedInterval (-446920034 / 1000000000000) (-446919653 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks1_2 :
    compactCertificate602.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1937255375973383 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34872853608 / 1000000000000) (34872853617 / 1000000000000), orderedInterval (9881721038 / 1000000000000) (9881721047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1642232836728463 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8028951663 / 1000000000000) (8028951677 / 1000000000000), orderedInterval (-38560484879 / 1000000000000) (-38560484864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1027633057909189 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4106046601 / 1000000000000) (4106046602 / 1000000000000), orderedInterval (49601980185 / 1000000000000) (49601980186 / 1000000000000)))) (orderedInterval (1152454583 / 1000000000000) (1152454695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (552664476296763 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44785958418 / 1000000000000) (44785958419 / 1000000000000), orderedInterval (50846380396 / 1000000000000) (50846380397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1500591561699289 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35899169000 / 1000000000000) (-35899112743 / 1000000000000), orderedInterval (20252626996 / 1000000000000) (20252683253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2048929487981753 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28426290675 / 1000000000000) (-28426290674 / 1000000000000), orderedInterval (-20823625461 / 1000000000000) (-20823625460 / 1000000000000)))) (orderedInterval (1088447805 / 1000000000000) (1088448868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (866366942090811 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30909505270 / 1000000000000) (-30909505269 / 1000000000000), orderedInterval (-44469266078 / 1000000000000) (-44469266077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3521733520344731 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26890009436 / 1000000000000) (26890014346 / 1000000000000), orderedInterval (-66282186 / 1000000000000) (-66277275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2352354780147829 / 4000000000000) 1 (IntervalRat.scale (947 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32400671759 / 1000000000000) (-32400671665 / 1000000000000), orderedInterval (-5692549025 / 1000000000000) (-5692548931 / 1000000000000)))) (orderedInterval (1213957421 / 1000000000000) (1213958370 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks1 :
    compactCertificate602.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate602.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate602_chunkChecks1_0
    compactCertificate602_chunkChecks1_1 compactCertificate602_chunkChecks1_2

theorem compactCertificate602_chunkChecks2_0 :
    compactCertificate602.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (947 / 2) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3491177877 / 1000000000000) (3491177879 / 1000000000000), orderedInterval (-36504513243 / 1000000000000) (-36504513241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1395111827662247 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31990182328 / 1000000000000) (-31990182327 / 1000000000000), orderedInterval (-28272238611 / 1000000000000) (-28272238610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (451150500684551 / 800000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23229031125 / 1000000000000) (-23229024518 / 1000000000000), orderedInterval (24295982589 / 1000000000000) (24295989197 / 1000000000000)))) (orderedInterval (738871277 / 1000000000000) (738871872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (407090151853429 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71045403964 / 1000000000000) (71045412992 / 1000000000000), orderedInterval (-35102789403 / 1000000000000) (-35102780376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1093501409844913 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-35989968284 / 1000000000000) (-35989968283 / 1000000000000), orderedInterval (-32081655177 / 1000000000000) (-32081655176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2969069044047021 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29222553915 / 1000000000000) (29222558517 / 1000000000000), orderedInterval (-1946139056 / 1000000000000) (-1946134453 / 1000000000000)))) (orderedInterval (5579535423 / 1000000000000) (5579536322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2187002819690773 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26702869926 / 1000000000000) (26702869927 / 1000000000000), orderedInterval (21220014878 / 1000000000000) (21220014879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3747466607809129 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25899908349 / 1000000000000) (25899910253 / 1000000000000), orderedInterval (2938253254 / 1000000000000) (2938255157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2760366942090811 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8201806616 / 1000000000000) (-8201806611 / 1000000000000), orderedInterval (29250519442 / 1000000000000) (29250519446 / 1000000000000)))) (orderedInterval (3546651674 / 1000000000000) (3546651987 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks2_1 :
    compactCertificate602.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4235112749384053 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18369316016 / 1000000000000) (-18369316015 / 1000000000000), orderedInterval (-16234661610 / 1000000000000) (-16234661609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2445143485905037 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16578109967 / 1000000000000) (16578110354 / 1000000000000), orderedInterval (-27701284032 / 1000000000000) (-27701283645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4338950023907633 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24098577471 / 1000000000000) (-24098541522 / 1000000000000), orderedInterval (2490539293 / 1000000000000) (2490575242 / 1000000000000)))) (orderedInterval (-397961065 / 1000000000000) (-397933338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4054009946128277 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10826098333 / 1000000000000) (10826098338 / 1000000000000), orderedInterval (-22609189846 / 1000000000000) (-22609189840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2893132788747941 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29597880626 / 1000000000000) (29597881535 / 1000000000000), orderedInterval (2015646620 / 1000000000000) (2015647529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3280504229534739 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22753457006 / 1000000000000) (-22753457005 / 1000000000000), orderedInterval (-16064883970 / 1000000000000) (-16064883969 / 1000000000000)))) (orderedInterval (-5983435787 / 1000000000000) (-5983435434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2734942416827491 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10359243757 / 1000000000000) (-10359243743 / 1000000000000), orderedInterval (28709088122 / 1000000000000) (28709088137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2416404567749311 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32189874775 / 1000000000000) (32189879088 / 1000000000000), orderedInterval (-4226793528 / 1000000000000) (-4226789215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (700368227625789 / 800000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6901513433 / 1000000000000) (6901513435 / 1000000000000), orderedInterval (-26072162581 / 1000000000000) (-26072162579 / 1000000000000)))) (orderedInterval (2644766282 / 1000000000000) (2644766783 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks2_2 :
    compactCertificate602.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1937255375973383 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34872853608 / 1000000000000) (34872853617 / 1000000000000), orderedInterval (9881721038 / 1000000000000) (9881721047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1642232836728463 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8028951663 / 1000000000000) (8028951677 / 1000000000000), orderedInterval (-38560484879 / 1000000000000) (-38560484864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1027633057909189 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4106046601 / 1000000000000) (4106046602 / 1000000000000), orderedInterval (49601980185 / 1000000000000) (49601980186 / 1000000000000)))) (orderedInterval (6133367184 / 1000000000000) (6133367291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (552664476296763 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44785958418 / 1000000000000) (44785958419 / 1000000000000), orderedInterval (50846380396 / 1000000000000) (50846380397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1500591561699289 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35899169000 / 1000000000000) (-35899112743 / 1000000000000), orderedInterval (20252626996 / 1000000000000) (20252683253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2048929487981753 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28426290675 / 1000000000000) (-28426290674 / 1000000000000), orderedInterval (-20823625461 / 1000000000000) (-20823625460 / 1000000000000)))) (orderedInterval (-2992672940 / 1000000000000) (-2992672086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (866366942090811 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30909505270 / 1000000000000) (-30909505269 / 1000000000000), orderedInterval (-44469266078 / 1000000000000) (-44469266077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3521733520344731 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26890009436 / 1000000000000) (26890014346 / 1000000000000), orderedInterval (-66282186 / 1000000000000) (-66277275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2352354780147829 / 4000000000000) 2 (IntervalRat.scale (947 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32400671759 / 1000000000000) (-32400671665 / 1000000000000), orderedInterval (-5692549025 / 1000000000000) (-5692548931 / 1000000000000)))) (orderedInterval (-1773280901 / 1000000000000) (-1773279218 / 1000000000000))) = true
  rfl'

theorem compactCertificate602_chunkChecks2 :
    compactCertificate602.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate602.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate602_chunkChecks2_0
    compactCertificate602_chunkChecks2_1 compactCertificate602_chunkChecks2_2

theorem compactCertificate602_chunkChecks3_0 :
    compactCertificate602.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (947 / 2) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3491177877 / 1000000000000) (3491177879 / 1000000000000), orderedInterval (-36504513243 / 1000000000000) (-36504513241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1395111827662247 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31990182328 / 1000000000000) (-31990182327 / 1000000000000), orderedInterval (-28272238611 / 1000000000000) (-28272238610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (451150500684551 / 800000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23229031125 / 1000000000000) (-23229024518 / 1000000000000), orderedInterval (24295982589 / 1000000000000) (24295989197 / 1000000000000)))) (orderedInterval (12164163476 / 1000000000000) (12164164182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (407090151853429 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71045403964 / 1000000000000) (71045412992 / 1000000000000), orderedInterval (-35102789403 / 1000000000000) (-35102780376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1093501409844913 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-35989968284 / 1000000000000) (-35989968283 / 1000000000000), orderedInterval (-32081655177 / 1000000000000) (-32081655176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2969069044047021 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29222553915 / 1000000000000) (29222558517 / 1000000000000), orderedInterval (-1946139056 / 1000000000000) (-1946134453 / 1000000000000)))) (orderedInterval (-323107168 / 1000000000000) (-323105771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2187002819690773 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26702869926 / 1000000000000) (26702869927 / 1000000000000), orderedInterval (21220014878 / 1000000000000) (21220014879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3747466607809129 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25899908349 / 1000000000000) (25899910253 / 1000000000000), orderedInterval (2938253254 / 1000000000000) (2938255157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2760366942090811 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8201806616 / 1000000000000) (-8201806611 / 1000000000000), orderedInterval (29250519442 / 1000000000000) (29250519446 / 1000000000000)))) (orderedInterval (-1493936042 / 1000000000000) (-1493935437 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate602_chunkChecks3_1 :
    compactCertificate602.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4235112749384053 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18369316016 / 1000000000000) (-18369316015 / 1000000000000), orderedInterval (-16234661610 / 1000000000000) (-16234661609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2445143485905037 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16578109967 / 1000000000000) (16578110354 / 1000000000000), orderedInterval (-27701284032 / 1000000000000) (-27701283645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4338950023907633 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24098577471 / 1000000000000) (-24098541522 / 1000000000000), orderedInterval (2490539293 / 1000000000000) (2490575242 / 1000000000000)))) (orderedInterval (-32091716213 / 1000000000000) (-32091652824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4054009946128277 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10826098333 / 1000000000000) (10826098338 / 1000000000000), orderedInterval (-22609189846 / 1000000000000) (-22609189840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2893132788747941 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29597880626 / 1000000000000) (29597881535 / 1000000000000), orderedInterval (2015646620 / 1000000000000) (2015647529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3280504229534739 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22753457006 / 1000000000000) (-22753457005 / 1000000000000), orderedInterval (-16064883970 / 1000000000000) (-16064883969 / 1000000000000)))) (orderedInterval (-5091833692 / 1000000000000) (-5091833127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2734942416827491 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10359243757 / 1000000000000) (-10359243743 / 1000000000000), orderedInterval (28709088122 / 1000000000000) (28709088137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2416404567749311 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32189874775 / 1000000000000) (32189879088 / 1000000000000), orderedInterval (-4226793528 / 1000000000000) (-4226789215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (700368227625789 / 800000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6901513433 / 1000000000000) (6901513435 / 1000000000000), orderedInterval (-26072162581 / 1000000000000) (-26072162579 / 1000000000000)))) (orderedInterval (2713124792 / 1000000000000) (2713125456 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate602_chunkChecks3_2 :
    compactCertificate602.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1937255375973383 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34872853608 / 1000000000000) (34872853617 / 1000000000000), orderedInterval (9881721038 / 1000000000000) (9881721047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1642232836728463 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8028951663 / 1000000000000) (8028951677 / 1000000000000), orderedInterval (-38560484879 / 1000000000000) (-38560484864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1027633057909189 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4106046601 / 1000000000000) (4106046602 / 1000000000000), orderedInterval (49601980185 / 1000000000000) (49601980186 / 1000000000000)))) (orderedInterval (-2847924 / 1000000000000) (-2847820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (552664476296763 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44785958418 / 1000000000000) (44785958419 / 1000000000000), orderedInterval (50846380396 / 1000000000000) (50846380397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1500591561699289 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35899169000 / 1000000000000) (-35899112743 / 1000000000000), orderedInterval (20252626996 / 1000000000000) (20252683253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2048929487981753 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28426290675 / 1000000000000) (-28426290674 / 1000000000000), orderedInterval (-20823625461 / 1000000000000) (-20823625460 / 1000000000000)))) (orderedInterval (-1762281688 / 1000000000000) (-1762280999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (866366942090811 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30909505270 / 1000000000000) (-30909505269 / 1000000000000), orderedInterval (-44469266078 / 1000000000000) (-44469266077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3521733520344731 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26890009436 / 1000000000000) (26890014346 / 1000000000000), orderedInterval (-66282186 / 1000000000000) (-66277275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2352354780147829 / 4000000000000) 3 (IntervalRat.scale (947 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32400671759 / 1000000000000) (-32400671665 / 1000000000000), orderedInterval (-5692549025 / 1000000000000) (-5692548931 / 1000000000000)))) (orderedInterval (-2051579462 / 1000000000000) (-2051576436 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate602_chunkChecks3 :
    compactCertificate602.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate602.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate602_chunkChecks3_0
    compactCertificate602_chunkChecks3_1 compactCertificate602_chunkChecks3_2

theorem compactCertificate602_chunkChecks4_0 :
    compactCertificate602.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (947 / 2) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (3491177877 / 1000000000000) (3491177879 / 1000000000000), orderedInterval (-36504513243 / 1000000000000) (-36504513241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1395111827662247 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31990182328 / 1000000000000) (-31990182327 / 1000000000000), orderedInterval (-28272238611 / 1000000000000) (-28272238610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (451150500684551 / 800000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23229031125 / 1000000000000) (-23229024518 / 1000000000000), orderedInterval (24295982589 / 1000000000000) (24295989197 / 1000000000000)))) (orderedInterval (-1498030456 / 1000000000000) (-1498029614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (407090151853429 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (71045403964 / 1000000000000) (71045412992 / 1000000000000), orderedInterval (-35102789403 / 1000000000000) (-35102780376 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1093501409844913 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-35989968284 / 1000000000000) (-35989968283 / 1000000000000), orderedInterval (-32081655177 / 1000000000000) (-32081655176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2969069044047021 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29222553915 / 1000000000000) (29222558517 / 1000000000000), orderedInterval (-1946139056 / 1000000000000) (-1946134453 / 1000000000000)))) (orderedInterval (-12691700342 / 1000000000000) (-12691698154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2187002819690773 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26702869926 / 1000000000000) (26702869927 / 1000000000000), orderedInterval (21220014878 / 1000000000000) (21220014879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3747466607809129 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25899908349 / 1000000000000) (25899910253 / 1000000000000), orderedInterval (2938253254 / 1000000000000) (2938255157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2760366942090811 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-8201806616 / 1000000000000) (-8201806611 / 1000000000000), orderedInterval (29250519442 / 1000000000000) (29250519446 / 1000000000000)))) (orderedInterval (-13131351683 / 1000000000000) (-13131350504 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate602_chunkChecks4_1 :
    compactCertificate602.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4235112749384053 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18369316016 / 1000000000000) (-18369316015 / 1000000000000), orderedInterval (-16234661610 / 1000000000000) (-16234661609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2445143485905037 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16578109967 / 1000000000000) (16578110354 / 1000000000000), orderedInterval (-27701284032 / 1000000000000) (-27701283645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4338950023907633 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24098577471 / 1000000000000) (-24098541522 / 1000000000000), orderedInterval (2490539293 / 1000000000000) (2490575242 / 1000000000000)))) (orderedInterval (-9209545370 / 1000000000000) (-9209400213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4054009946128277 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10826098333 / 1000000000000) (10826098338 / 1000000000000), orderedInterval (-22609189846 / 1000000000000) (-22609189840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2893132788747941 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29597880626 / 1000000000000) (29597881535 / 1000000000000), orderedInterval (2015646620 / 1000000000000) (2015647529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3280504229534739 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22753457006 / 1000000000000) (-22753457005 / 1000000000000), orderedInterval (-16064883970 / 1000000000000) (-16064883969 / 1000000000000)))) (orderedInterval (12193585815 / 1000000000000) (12193586732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2734942416827491 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10359243757 / 1000000000000) (-10359243743 / 1000000000000), orderedInterval (28709088122 / 1000000000000) (28709088137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2416404567749311 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32189874775 / 1000000000000) (32189879088 / 1000000000000), orderedInterval (-4226793528 / 1000000000000) (-4226789215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (700368227625789 / 800000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6901513433 / 1000000000000) (6901513435 / 1000000000000), orderedInterval (-26072162581 / 1000000000000) (-26072162579 / 1000000000000)))) (orderedInterval (-3347209651 / 1000000000000) (-3347208755 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate602_chunkChecks4_2 :
    compactCertificate602.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1937255375973383 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34872853608 / 1000000000000) (34872853617 / 1000000000000), orderedInterval (9881721038 / 1000000000000) (9881721047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1642232836728463 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (8028951663 / 1000000000000) (8028951677 / 1000000000000), orderedInterval (-38560484879 / 1000000000000) (-38560484864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1027633057909189 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4106046601 / 1000000000000) (4106046602 / 1000000000000), orderedInterval (49601980185 / 1000000000000) (49601980186 / 1000000000000)))) (orderedInterval (-6348229801 / 1000000000000) (-6348229699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (552664476296763 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44785958418 / 1000000000000) (44785958419 / 1000000000000), orderedInterval (50846380396 / 1000000000000) (50846380397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1500591561699289 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35899169000 / 1000000000000) (-35899112743 / 1000000000000), orderedInterval (20252626996 / 1000000000000) (20252683253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2048929487981753 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-28426290675 / 1000000000000) (-28426290674 / 1000000000000), orderedInterval (-20823625461 / 1000000000000) (-20823625460 / 1000000000000)))) (orderedInterval (3306064202 / 1000000000000) (3306064763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (866366942090811 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30909505270 / 1000000000000) (-30909505269 / 1000000000000), orderedInterval (-44469266078 / 1000000000000) (-44469266077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3521733520344731 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26890009436 / 1000000000000) (26890014346 / 1000000000000), orderedInterval (-66282186 / 1000000000000) (-66277275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2352354780147829 / 4000000000000) 4 (IntervalRat.scale (947 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32400671759 / 1000000000000) (-32400671665 / 1000000000000), orderedInterval (-5692549025 / 1000000000000) (-5692548931 / 1000000000000)))) (orderedInterval (-11699411533 / 1000000000000) (-11699406029 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate602_chunkChecks4 :
    compactCertificate602.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate602.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate602_chunkChecks4_0
    compactCertificate602_chunkChecks4_1 compactCertificate602_chunkChecks4_2

theorem compactCertificate602_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate602.chunkCheck r b = true :=
  compactCertificate602.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate602_chunkChecks0
    · exact compactCertificate602_chunkChecks1
    · exact compactCertificate602_chunkChecks2
    · exact compactCertificate602_chunkChecks3
    · exact compactCertificate602_chunkChecks4)

theorem compactCertificate602_coefficient0 :
    compactCertificate602.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate602_coefficient1 :
    compactCertificate602.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate602_coefficient2 :
    compactCertificate602.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate602_coefficient3 :
    compactCertificate602.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate602_coefficient4 :
    compactCertificate602.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate602_coefficients : ∀ r : Fin 5,
    compactCertificate602.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate602_coefficient0
  · exact compactCertificate602_coefficient1
  · exact compactCertificate602_coefficient2
  · exact compactCertificate602_coefficient3
  · exact compactCertificate602_coefficient4

theorem compactCertificate602_lower : (1 : ℚ) ≤ compactCertificate602.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate602, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate602_proves {t : ℝ} (ht : t ∈ compactCertificate602.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate602.proves compactCertificate602_states compactCertificate602_chunks
    compactCertificate602_coefficients compactCertificate602_lower ht

end Erdos232
