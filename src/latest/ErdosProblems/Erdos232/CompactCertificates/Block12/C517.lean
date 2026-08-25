/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate517 : CompactCertificate where
  left := 388
  right := 389
  center := 777 / 2
  grid := fun i =>
    match i.val with
    | 0 => 124
    | 1 => 91
    | 2 => 147
    | 3 => 27
    | 4 => 71
    | 5 => 194
    | 6 => 143
    | 7 => 245
    | 8 => 180
    | 9 => 277
    | 10 => 160
    | 11 => 283
    | 12 => 265
    | 13 => 189
    | 14 => 214
    | 15 => 179
    | 16 => 158
    | 17 => 229
    | 18 => 127
    | 19 => 107
    | 20 => 67
    | 21 => 36
    | 22 => 98
    | 23 => 134
    | 24 => 57
    | 25 => 230
    | _ => 154
  point := fun i =>
    match i.val with
    | 0 => 777 / 2
    | 1 => 1144669366519077 / 4000000000000
    | 2 => 370162554415941 / 800000000000
    | 3 => 334011666304239 / 4000000000000
    | 4 => 897202318320483 / 4000000000000
    | 5 => 2436078824946711 / 4000000000000
    | 6 => 1794404636641743 / 4000000000000
    | 7 => 3074742929532939 / 4000000000000
    | 8 => 2264841725453601 / 4000000000000
    | 9 => 3474849637034223 / 4000000000000
    | 10 => 2006205373334967 / 4000000000000
    | 11 => 3560046640524003 / 4000000000000
    | 12 => 3326257368681807 / 4000000000000
    | 13 => 2373774209986431 / 4000000000000
    | 14 => 2691606954961449 / 4000000000000
    | 15 => 2243981264915481 / 4000000000000
    | 16 => 1982625500677101 / 4000000000000
    | 17 => 574642146636999 / 800000000000
    | 18 => 1589490419357253 / 4000000000000
    | 19 => 1347428631613533 / 4000000000000
    | 20 => 843158274546399 / 4000000000000
    | 21 => 453453324268833 / 4000000000000
    | 22 => 1231213984625499 / 4000000000000
    | 23 => 1681117436284923 / 4000000000000
    | 24 => 710841725453601 / 4000000000000
    | 25 => 2889532149216321 / 4000000000000
    | _ => 1930073563014639 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-10891479070 / 1000000000000) (-10891479024 / 1000000000000), orderedInterval (39001679163 / 1000000000000) (39001679209 / 1000000000000))
    | 1 => (orderedInterval (-41314434320 / 1000000000000) (-41314434319 / 1000000000000), orderedInterval (-22682095352 / 1000000000000) (-22682095351 / 1000000000000))
    | 2 => (orderedInterval (-36894590519 / 1000000000000) (-36894589064 / 1000000000000), orderedInterval (3868597285 / 1000000000000) (3868598740 / 1000000000000))
    | 3 => (orderedInterval (44605290995 / 1000000000000) (44605298715 / 1000000000000), orderedInterval (-75329426837 / 1000000000000) (-75329419116 / 1000000000000))
    | 4 => (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))
    | 5 => (orderedInterval (10657782594 / 1000000000000) (10657782595 / 1000000000000), orderedInterval (30515515569 / 1000000000000) (30515515570 / 1000000000000))
    | 6 => (orderedInterval (-5201890166 / 1000000000000) (-5201890165 / 1000000000000), orderedInterval (-37304565044 / 1000000000000) (-37304565043 / 1000000000000))
    | 7 => (orderedInterval (6258719016 / 1000000000000) (6258719018 / 1000000000000), orderedInterval (-28093590681 / 1000000000000) (-28093590679 / 1000000000000))
    | 8 => (orderedInterval (33467203309 / 1000000000000) (33467203678 / 1000000000000), orderedInterval (2043548074 / 1000000000000) (2043548443 / 1000000000000))
    | 9 => (orderedInterval (17921261431 / 1000000000000) (17921262183 / 1000000000000), orderedInterval (-20299717308 / 1000000000000) (-20299716555 / 1000000000000))
    | 10 => (orderedInterval (-11150725517 / 1000000000000) (-11150725478 / 1000000000000), orderedInterval (33848420006 / 1000000000000) (33848420045 / 1000000000000))
    | 11 => (orderedInterval (-26422698185 / 1000000000000) (-26422674597 / 1000000000000), orderedInterval (4154308513 / 1000000000000) (4154332101 / 1000000000000))
    | 12 => (orderedInterval (4748248616 / 1000000000000) (4748248617 / 1000000000000), orderedInterval (-27261305692 / 1000000000000) (-27261305691 / 1000000000000))
    | 13 => (orderedInterval (-14766987415 / 1000000000000) (-14766987414 / 1000000000000), orderedInterval (-29222669027 / 1000000000000) (-29222669026 / 1000000000000))
    | 14 => (orderedInterval (30235424852 / 1000000000000) (30235425000 / 1000000000000), orderedInterval (5625556726 / 1000000000000) (5625556874 / 1000000000000))
    | 15 => (orderedInterval (18024900668 / 1000000000000) (18024901394 / 1000000000000), orderedInterval (-28474934241 / 1000000000000) (-28474933514 / 1000000000000))
    | 16 => (orderedInterval (2502422391 / 1000000000000) (2502422392 / 1000000000000), orderedInterval (35748502980 / 1000000000000) (35748502981 / 1000000000000))
    | 17 => (orderedInterval (9838505321 / 1000000000000) (9838505331 / 1000000000000), orderedInterval (-28104667213 / 1000000000000) (-28104667203 / 1000000000000))
    | 18 => (orderedInterval (29389461271 / 1000000000000) (29389488572 / 1000000000000), orderedInterval (-27209244770 / 1000000000000) (-27209217470 / 1000000000000))
    | 19 => (orderedInterval (-43337059035 / 1000000000000) (-43337058976 / 1000000000000), orderedInterval (-3367548129 / 1000000000000) (-3367548069 / 1000000000000))
    | 20 => (orderedInterval (-48665989646 / 1000000000000) (-48665989645 / 1000000000000), orderedInterval (-25414623402 / 1000000000000) (-25414623401 / 1000000000000))
    | 21 => (orderedInterval (65013745995 / 1000000000000) (65013745996 / 1000000000000), orderedInterval (36981635599 / 1000000000000) (36981635600 / 1000000000000))
    | 22 => (orderedInterval (29727177438 / 1000000000000) (29727177439 / 1000000000000), orderedInterval (34369180091 / 1000000000000) (34369180092 / 1000000000000))
    | 23 => (orderedInterval (3538532366 / 1000000000000) (3538532367 / 1000000000000), orderedInterval (38754449704 / 1000000000000) (38754449705 / 1000000000000))
    | 24 => (orderedInterval (32582799142 / 1000000000000) (32582806293 / 1000000000000), orderedInterval (-50298349711 / 1000000000000) (-50298342560 / 1000000000000))
    | 25 => (orderedInterval (16809949186 / 1000000000000) (16809949187 / 1000000000000), orderedInterval (24456772808 / 1000000000000) (24456772809 / 1000000000000))
    | _ => (orderedInterval (-17469626501 / 1000000000000) (-17469625955 / 1000000000000), orderedInterval (31864318176 / 1000000000000) (31864318723 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-6866988048 / 1000000000000) (-6866987917 / 1000000000000)
      | 1 => orderedInterval (-2983229114 / 1000000000000) (-2983228341 / 1000000000000)
      | 2 => orderedInterval (615792326 / 1000000000000) (615792358 / 1000000000000)
      | 3 => orderedInterval (-7766711217 / 1000000000000) (-7766707573 / 1000000000000)
      | 4 => orderedInterval (-1635137882 / 1000000000000) (-1635137835 / 1000000000000)
      | 5 => orderedInterval (316844866 / 1000000000000) (316844913 / 1000000000000)
      | 6 => orderedInterval (-3830615996 / 1000000000000) (-3830611530 / 1000000000000)
      | 7 => orderedInterval (-2146091944 / 1000000000000) (-2146091897 / 1000000000000)
      | _ => orderedInterval (2105825257 / 1000000000000) (2105825511 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15573591653 / 1000000000000) (15573591804 / 1000000000000)
      | 1 => orderedInterval (-2722660838 / 1000000000000) (-2722660396 / 1000000000000)
      | 2 => orderedInterval (1786473313 / 1000000000000) (1786473365 / 1000000000000)
      | 3 => orderedInterval (12656108863 / 1000000000000) (12656117167 / 1000000000000)
      | 4 => orderedInterval (-3217017340 / 1000000000000) (-3217017263 / 1000000000000)
      | 5 => orderedInterval (-4415309551 / 1000000000000) (-4415309485 / 1000000000000)
      | 6 => orderedInterval (4166258969 / 1000000000000) (4166263528 / 1000000000000)
      | 7 => orderedInterval (-4030080510 / 1000000000000) (-4030080468 / 1000000000000)
      | _ => orderedInterval (-11265901826 / 1000000000000) (-11265901527 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (7556819776 / 1000000000000) (7556819951 / 1000000000000)
      | 1 => orderedInterval (2471798902 / 1000000000000) (2471799195 / 1000000000000)
      | 2 => orderedInterval (-966903667 / 1000000000000) (-966903580 / 1000000000000)
      | 3 => orderedInterval (36979264602 / 1000000000000) (36979283578 / 1000000000000)
      | 4 => orderedInterval (4118323846 / 1000000000000) (4118323973 / 1000000000000)
      | 5 => orderedInterval (-1050681609 / 1000000000000) (-1050681510 / 1000000000000)
      | 6 => orderedInterval (3527821615 / 1000000000000) (3527826282 / 1000000000000)
      | 7 => orderedInterval (853303871 / 1000000000000) (853303913 / 1000000000000)
      | _ => orderedInterval (-337288386 / 1000000000000) (-337287995 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15777298510 / 1000000000000) (-15777298306 / 1000000000000)
      | 1 => orderedInterval (8175001258 / 1000000000000) (8175001494 / 1000000000000)
      | 2 => orderedInterval (-6862382846 / 1000000000000) (-6862382695 / 1000000000000)
      | 3 => orderedInterval (-52919225958 / 1000000000000) (-52919182595 / 1000000000000)
      | 4 => orderedInterval (5160331115 / 1000000000000) (5160331330 / 1000000000000)
      | 5 => orderedInterval (9789286053 / 1000000000000) (9789286204 / 1000000000000)
      | 6 => orderedInterval (-4656635807 / 1000000000000) (-4656631038 / 1000000000000)
      | 7 => orderedInterval (4162735400 / 1000000000000) (4162735444 / 1000000000000)
      | _ => orderedInterval (24282688005 / 1000000000000) (24282688551 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8705252447 / 1000000000000) (-8705252208 / 1000000000000)
      | 1 => orderedInterval (-4812073361 / 1000000000000) (-4812073119 / 1000000000000)
      | 2 => orderedInterval (726000310 / 1000000000000) (726000578 / 1000000000000)
      | 3 => orderedInterval (-185089262861 / 1000000000000) (-185089163611 / 1000000000000)
      | 4 => orderedInterval (-10805588321 / 1000000000000) (-10805587947 / 1000000000000)
      | 5 => orderedInterval (3418919122 / 1000000000000) (3418919357 / 1000000000000)
      | 6 => orderedInterval (-3870255550 / 1000000000000) (-3870250664 / 1000000000000)
      | 7 => orderedInterval (-667283993 / 1000000000000) (-667283947 / 1000000000000)
      | _ => orderedInterval (-8673967417 / 1000000000000) (-8673966617 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-22190311752 / 1000000000000) (-22190302311 / 1000000000000)
    | 1 => orderedInterval (8531462733 / 1000000000000) (8531476725 / 1000000000000)
    | 2 => orderedInterval (53152458950 / 1000000000000) (53152483807 / 1000000000000)
    | 3 => orderedInterval (-28645501290 / 1000000000000) (-28645451611 / 1000000000000)
    | _ => orderedInterval (-218478764518 / 1000000000000) (-218478658178 / 1000000000000)

theorem compactCertificate517_stateChecks0 :
    compactCertificate517.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (777 / 2)) (orderedInterval (-10891479070 / 1000000000000) (-10891479024 / 1000000000000), orderedInterval (39001679163 / 1000000000000) (39001679209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1144669366519077 / 4000000000000)) (orderedInterval (-41314434320 / 1000000000000) (-41314434319 / 1000000000000), orderedInterval (-22682095352 / 1000000000000) (-22682095351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (370162554415941 / 800000000000)) (orderedInterval (-36894590519 / 1000000000000) (-36894589064 / 1000000000000), orderedInterval (3868597285 / 1000000000000) (3868598740 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_stateChecks1 :
    compactCertificate517.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (334011666304239 / 4000000000000)) (orderedInterval (44605290995 / 1000000000000) (44605298715 / 1000000000000), orderedInterval (-75329426837 / 1000000000000) (-75329419116 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (897202318320483 / 4000000000000)) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2436078824946711 / 4000000000000)) (orderedInterval (10657782594 / 1000000000000) (10657782595 / 1000000000000), orderedInterval (30515515569 / 1000000000000) (30515515570 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_stateChecks2 :
    compactCertificate517.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1794404636641743 / 4000000000000)) (orderedInterval (-5201890166 / 1000000000000) (-5201890165 / 1000000000000), orderedInterval (-37304565044 / 1000000000000) (-37304565043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3074742929532939 / 4000000000000)) (orderedInterval (6258719016 / 1000000000000) (6258719018 / 1000000000000), orderedInterval (-28093590681 / 1000000000000) (-28093590679 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2264841725453601 / 4000000000000)) (orderedInterval (33467203309 / 1000000000000) (33467203678 / 1000000000000), orderedInterval (2043548074 / 1000000000000) (2043548443 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_stateChecks3 :
    compactCertificate517.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 277 12 (3474849637034223 / 4000000000000)) (orderedInterval (17921261431 / 1000000000000) (17921262183 / 1000000000000), orderedInterval (-20299717308 / 1000000000000) (-20299716555 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2006205373334967 / 4000000000000)) (orderedInterval (-11150725517 / 1000000000000) (-11150725478 / 1000000000000), orderedInterval (33848420006 / 1000000000000) (33848420045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (3560046640524003 / 4000000000000)) (orderedInterval (-26422698185 / 1000000000000) (-26422674597 / 1000000000000), orderedInterval (4154308513 / 1000000000000) (4154332101 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_stateChecks4 :
    compactCertificate517.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (3326257368681807 / 4000000000000)) (orderedInterval (4748248616 / 1000000000000) (4748248617 / 1000000000000), orderedInterval (-27261305692 / 1000000000000) (-27261305691 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2373774209986431 / 4000000000000)) (orderedInterval (-14766987415 / 1000000000000) (-14766987414 / 1000000000000), orderedInterval (-29222669027 / 1000000000000) (-29222669026 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2691606954961449 / 4000000000000)) (orderedInterval (30235424852 / 1000000000000) (30235425000 / 1000000000000), orderedInterval (5625556726 / 1000000000000) (5625556874 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_stateChecks5 :
    compactCertificate517.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2243981264915481 / 4000000000000)) (orderedInterval (18024900668 / 1000000000000) (18024901394 / 1000000000000), orderedInterval (-28474934241 / 1000000000000) (-28474933514 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1982625500677101 / 4000000000000)) (orderedInterval (2502422391 / 1000000000000) (2502422392 / 1000000000000), orderedInterval (35748502980 / 1000000000000) (35748502981 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (574642146636999 / 800000000000)) (orderedInterval (9838505321 / 1000000000000) (9838505331 / 1000000000000), orderedInterval (-28104667213 / 1000000000000) (-28104667203 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_stateChecks6 :
    compactCertificate517.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1589490419357253 / 4000000000000)) (orderedInterval (29389461271 / 1000000000000) (29389488572 / 1000000000000), orderedInterval (-27209244770 / 1000000000000) (-27209217470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1347428631613533 / 4000000000000)) (orderedInterval (-43337059035 / 1000000000000) (-43337058976 / 1000000000000), orderedInterval (-3367548129 / 1000000000000) (-3367548069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (843158274546399 / 4000000000000)) (orderedInterval (-48665989646 / 1000000000000) (-48665989645 / 1000000000000), orderedInterval (-25414623402 / 1000000000000) (-25414623401 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_stateChecks7 :
    compactCertificate517.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (453453324268833 / 4000000000000)) (orderedInterval (65013745995 / 1000000000000) (65013745996 / 1000000000000), orderedInterval (36981635599 / 1000000000000) (36981635600 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1231213984625499 / 4000000000000)) (orderedInterval (29727177438 / 1000000000000) (29727177439 / 1000000000000), orderedInterval (34369180091 / 1000000000000) (34369180092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1681117436284923 / 4000000000000)) (orderedInterval (3538532366 / 1000000000000) (3538532367 / 1000000000000), orderedInterval (38754449704 / 1000000000000) (38754449705 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_stateChecks8 :
    compactCertificate517.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (710841725453601 / 4000000000000)) (orderedInterval (32582799142 / 1000000000000) (32582806293 / 1000000000000), orderedInterval (-50298349711 / 1000000000000) (-50298342560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2889532149216321 / 4000000000000)) (orderedInterval (16809949186 / 1000000000000) (16809949187 / 1000000000000), orderedInterval (24456772808 / 1000000000000) (24456772809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1930073563014639 / 4000000000000)) (orderedInterval (-17469626501 / 1000000000000) (-17469625955 / 1000000000000), orderedInterval (31864318176 / 1000000000000) (31864318723 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_states : ∀ j,
    BesselStateValid (compactCertificate517.point j) (compactCertificate517.state j) :=
  compactCertificate517.statesValid_of_checks3 compactCertificate517_stateChecks0
    compactCertificate517_stateChecks1 compactCertificate517_stateChecks2
    compactCertificate517_stateChecks3 compactCertificate517_stateChecks4
    compactCertificate517_stateChecks5 compactCertificate517_stateChecks6
    compactCertificate517_stateChecks7 compactCertificate517_stateChecks8

theorem compactCertificate517_chunkChecks0_0 :
    compactCertificate517.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (777 / 2) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10891479070 / 1000000000000) (-10891479024 / 1000000000000), orderedInterval (39001679163 / 1000000000000) (39001679209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1144669366519077 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41314434320 / 1000000000000) (-41314434319 / 1000000000000), orderedInterval (-22682095352 / 1000000000000) (-22682095351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (370162554415941 / 800000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36894590519 / 1000000000000) (-36894589064 / 1000000000000), orderedInterval (3868597285 / 1000000000000) (3868598740 / 1000000000000)))) (orderedInterval (-6866988048 / 1000000000000) (-6866987917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (334011666304239 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44605290995 / 1000000000000) (44605298715 / 1000000000000), orderedInterval (-75329426837 / 1000000000000) (-75329419116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2436078824946711 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10657782594 / 1000000000000) (10657782595 / 1000000000000), orderedInterval (30515515569 / 1000000000000) (30515515570 / 1000000000000)))) (orderedInterval (-2983229114 / 1000000000000) (-2983228341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1794404636641743 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5201890166 / 1000000000000) (-5201890165 / 1000000000000), orderedInterval (-37304565044 / 1000000000000) (-37304565043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3074742929532939 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6258719016 / 1000000000000) (6258719018 / 1000000000000), orderedInterval (-28093590681 / 1000000000000) (-28093590679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2264841725453601 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33467203309 / 1000000000000) (33467203678 / 1000000000000), orderedInterval (2043548074 / 1000000000000) (2043548443 / 1000000000000)))) (orderedInterval (615792326 / 1000000000000) (615792358 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks0_1 :
    compactCertificate517.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3474849637034223 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17921261431 / 1000000000000) (17921262183 / 1000000000000), orderedInterval (-20299717308 / 1000000000000) (-20299716555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2006205373334967 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11150725517 / 1000000000000) (-11150725478 / 1000000000000), orderedInterval (33848420006 / 1000000000000) (33848420045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3560046640524003 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26422698185 / 1000000000000) (-26422674597 / 1000000000000), orderedInterval (4154308513 / 1000000000000) (4154332101 / 1000000000000)))) (orderedInterval (-7766711217 / 1000000000000) (-7766707573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3326257368681807 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4748248616 / 1000000000000) (4748248617 / 1000000000000), orderedInterval (-27261305692 / 1000000000000) (-27261305691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2373774209986431 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14766987415 / 1000000000000) (-14766987414 / 1000000000000), orderedInterval (-29222669027 / 1000000000000) (-29222669026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2691606954961449 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30235424852 / 1000000000000) (30235425000 / 1000000000000), orderedInterval (5625556726 / 1000000000000) (5625556874 / 1000000000000)))) (orderedInterval (-1635137882 / 1000000000000) (-1635137835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2243981264915481 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18024900668 / 1000000000000) (18024901394 / 1000000000000), orderedInterval (-28474934241 / 1000000000000) (-28474933514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1982625500677101 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2502422391 / 1000000000000) (2502422392 / 1000000000000), orderedInterval (35748502980 / 1000000000000) (35748502981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (574642146636999 / 800000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9838505321 / 1000000000000) (9838505331 / 1000000000000), orderedInterval (-28104667213 / 1000000000000) (-28104667203 / 1000000000000)))) (orderedInterval (316844866 / 1000000000000) (316844913 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks0_2 :
    compactCertificate517.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1589490419357253 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29389461271 / 1000000000000) (29389488572 / 1000000000000), orderedInterval (-27209244770 / 1000000000000) (-27209217470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1347428631613533 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43337059035 / 1000000000000) (-43337058976 / 1000000000000), orderedInterval (-3367548129 / 1000000000000) (-3367548069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (843158274546399 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48665989646 / 1000000000000) (-48665989645 / 1000000000000), orderedInterval (-25414623402 / 1000000000000) (-25414623401 / 1000000000000)))) (orderedInterval (-3830615996 / 1000000000000) (-3830611530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (453453324268833 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65013745995 / 1000000000000) (65013745996 / 1000000000000), orderedInterval (36981635599 / 1000000000000) (36981635600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1231213984625499 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29727177438 / 1000000000000) (29727177439 / 1000000000000), orderedInterval (34369180091 / 1000000000000) (34369180092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1681117436284923 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3538532366 / 1000000000000) (3538532367 / 1000000000000), orderedInterval (38754449704 / 1000000000000) (38754449705 / 1000000000000)))) (orderedInterval (-2146091944 / 1000000000000) (-2146091897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (710841725453601 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32582799142 / 1000000000000) (32582806293 / 1000000000000), orderedInterval (-50298349711 / 1000000000000) (-50298342560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2889532149216321 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16809949186 / 1000000000000) (16809949187 / 1000000000000), orderedInterval (24456772808 / 1000000000000) (24456772809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1930073563014639 / 4000000000000) 0 (IntervalRat.scale (777 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17469626501 / 1000000000000) (-17469625955 / 1000000000000), orderedInterval (31864318176 / 1000000000000) (31864318723 / 1000000000000)))) (orderedInterval (2105825257 / 1000000000000) (2105825511 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks0 :
    compactCertificate517.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate517.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate517_chunkChecks0_0
    compactCertificate517_chunkChecks0_1 compactCertificate517_chunkChecks0_2

theorem compactCertificate517_chunkChecks1_0 :
    compactCertificate517.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (777 / 2) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10891479070 / 1000000000000) (-10891479024 / 1000000000000), orderedInterval (39001679163 / 1000000000000) (39001679209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1144669366519077 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41314434320 / 1000000000000) (-41314434319 / 1000000000000), orderedInterval (-22682095352 / 1000000000000) (-22682095351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (370162554415941 / 800000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36894590519 / 1000000000000) (-36894589064 / 1000000000000), orderedInterval (3868597285 / 1000000000000) (3868598740 / 1000000000000)))) (orderedInterval (15573591653 / 1000000000000) (15573591804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (334011666304239 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44605290995 / 1000000000000) (44605298715 / 1000000000000), orderedInterval (-75329426837 / 1000000000000) (-75329419116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2436078824946711 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10657782594 / 1000000000000) (10657782595 / 1000000000000), orderedInterval (30515515569 / 1000000000000) (30515515570 / 1000000000000)))) (orderedInterval (-2722660838 / 1000000000000) (-2722660396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1794404636641743 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5201890166 / 1000000000000) (-5201890165 / 1000000000000), orderedInterval (-37304565044 / 1000000000000) (-37304565043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3074742929532939 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6258719016 / 1000000000000) (6258719018 / 1000000000000), orderedInterval (-28093590681 / 1000000000000) (-28093590679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2264841725453601 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33467203309 / 1000000000000) (33467203678 / 1000000000000), orderedInterval (2043548074 / 1000000000000) (2043548443 / 1000000000000)))) (orderedInterval (1786473313 / 1000000000000) (1786473365 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks1_1 :
    compactCertificate517.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3474849637034223 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17921261431 / 1000000000000) (17921262183 / 1000000000000), orderedInterval (-20299717308 / 1000000000000) (-20299716555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2006205373334967 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11150725517 / 1000000000000) (-11150725478 / 1000000000000), orderedInterval (33848420006 / 1000000000000) (33848420045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3560046640524003 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26422698185 / 1000000000000) (-26422674597 / 1000000000000), orderedInterval (4154308513 / 1000000000000) (4154332101 / 1000000000000)))) (orderedInterval (12656108863 / 1000000000000) (12656117167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3326257368681807 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4748248616 / 1000000000000) (4748248617 / 1000000000000), orderedInterval (-27261305692 / 1000000000000) (-27261305691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2373774209986431 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14766987415 / 1000000000000) (-14766987414 / 1000000000000), orderedInterval (-29222669027 / 1000000000000) (-29222669026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2691606954961449 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30235424852 / 1000000000000) (30235425000 / 1000000000000), orderedInterval (5625556726 / 1000000000000) (5625556874 / 1000000000000)))) (orderedInterval (-3217017340 / 1000000000000) (-3217017263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2243981264915481 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18024900668 / 1000000000000) (18024901394 / 1000000000000), orderedInterval (-28474934241 / 1000000000000) (-28474933514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1982625500677101 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2502422391 / 1000000000000) (2502422392 / 1000000000000), orderedInterval (35748502980 / 1000000000000) (35748502981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (574642146636999 / 800000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9838505321 / 1000000000000) (9838505331 / 1000000000000), orderedInterval (-28104667213 / 1000000000000) (-28104667203 / 1000000000000)))) (orderedInterval (-4415309551 / 1000000000000) (-4415309485 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks1_2 :
    compactCertificate517.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1589490419357253 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29389461271 / 1000000000000) (29389488572 / 1000000000000), orderedInterval (-27209244770 / 1000000000000) (-27209217470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1347428631613533 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43337059035 / 1000000000000) (-43337058976 / 1000000000000), orderedInterval (-3367548129 / 1000000000000) (-3367548069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (843158274546399 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48665989646 / 1000000000000) (-48665989645 / 1000000000000), orderedInterval (-25414623402 / 1000000000000) (-25414623401 / 1000000000000)))) (orderedInterval (4166258969 / 1000000000000) (4166263528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (453453324268833 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65013745995 / 1000000000000) (65013745996 / 1000000000000), orderedInterval (36981635599 / 1000000000000) (36981635600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1231213984625499 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29727177438 / 1000000000000) (29727177439 / 1000000000000), orderedInterval (34369180091 / 1000000000000) (34369180092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1681117436284923 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3538532366 / 1000000000000) (3538532367 / 1000000000000), orderedInterval (38754449704 / 1000000000000) (38754449705 / 1000000000000)))) (orderedInterval (-4030080510 / 1000000000000) (-4030080468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (710841725453601 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32582799142 / 1000000000000) (32582806293 / 1000000000000), orderedInterval (-50298349711 / 1000000000000) (-50298342560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2889532149216321 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16809949186 / 1000000000000) (16809949187 / 1000000000000), orderedInterval (24456772808 / 1000000000000) (24456772809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1930073563014639 / 4000000000000) 1 (IntervalRat.scale (777 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17469626501 / 1000000000000) (-17469625955 / 1000000000000), orderedInterval (31864318176 / 1000000000000) (31864318723 / 1000000000000)))) (orderedInterval (-11265901826 / 1000000000000) (-11265901527 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks1 :
    compactCertificate517.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate517.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate517_chunkChecks1_0
    compactCertificate517_chunkChecks1_1 compactCertificate517_chunkChecks1_2

theorem compactCertificate517_chunkChecks2_0 :
    compactCertificate517.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (777 / 2) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10891479070 / 1000000000000) (-10891479024 / 1000000000000), orderedInterval (39001679163 / 1000000000000) (39001679209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1144669366519077 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41314434320 / 1000000000000) (-41314434319 / 1000000000000), orderedInterval (-22682095352 / 1000000000000) (-22682095351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (370162554415941 / 800000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36894590519 / 1000000000000) (-36894589064 / 1000000000000), orderedInterval (3868597285 / 1000000000000) (3868598740 / 1000000000000)))) (orderedInterval (7556819776 / 1000000000000) (7556819951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (334011666304239 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44605290995 / 1000000000000) (44605298715 / 1000000000000), orderedInterval (-75329426837 / 1000000000000) (-75329419116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2436078824946711 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10657782594 / 1000000000000) (10657782595 / 1000000000000), orderedInterval (30515515569 / 1000000000000) (30515515570 / 1000000000000)))) (orderedInterval (2471798902 / 1000000000000) (2471799195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1794404636641743 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5201890166 / 1000000000000) (-5201890165 / 1000000000000), orderedInterval (-37304565044 / 1000000000000) (-37304565043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3074742929532939 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6258719016 / 1000000000000) (6258719018 / 1000000000000), orderedInterval (-28093590681 / 1000000000000) (-28093590679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2264841725453601 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33467203309 / 1000000000000) (33467203678 / 1000000000000), orderedInterval (2043548074 / 1000000000000) (2043548443 / 1000000000000)))) (orderedInterval (-966903667 / 1000000000000) (-966903580 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks2_1 :
    compactCertificate517.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3474849637034223 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17921261431 / 1000000000000) (17921262183 / 1000000000000), orderedInterval (-20299717308 / 1000000000000) (-20299716555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2006205373334967 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11150725517 / 1000000000000) (-11150725478 / 1000000000000), orderedInterval (33848420006 / 1000000000000) (33848420045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3560046640524003 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26422698185 / 1000000000000) (-26422674597 / 1000000000000), orderedInterval (4154308513 / 1000000000000) (4154332101 / 1000000000000)))) (orderedInterval (36979264602 / 1000000000000) (36979283578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3326257368681807 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4748248616 / 1000000000000) (4748248617 / 1000000000000), orderedInterval (-27261305692 / 1000000000000) (-27261305691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2373774209986431 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14766987415 / 1000000000000) (-14766987414 / 1000000000000), orderedInterval (-29222669027 / 1000000000000) (-29222669026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2691606954961449 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30235424852 / 1000000000000) (30235425000 / 1000000000000), orderedInterval (5625556726 / 1000000000000) (5625556874 / 1000000000000)))) (orderedInterval (4118323846 / 1000000000000) (4118323973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2243981264915481 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18024900668 / 1000000000000) (18024901394 / 1000000000000), orderedInterval (-28474934241 / 1000000000000) (-28474933514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1982625500677101 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2502422391 / 1000000000000) (2502422392 / 1000000000000), orderedInterval (35748502980 / 1000000000000) (35748502981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (574642146636999 / 800000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9838505321 / 1000000000000) (9838505331 / 1000000000000), orderedInterval (-28104667213 / 1000000000000) (-28104667203 / 1000000000000)))) (orderedInterval (-1050681609 / 1000000000000) (-1050681510 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks2_2 :
    compactCertificate517.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1589490419357253 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29389461271 / 1000000000000) (29389488572 / 1000000000000), orderedInterval (-27209244770 / 1000000000000) (-27209217470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1347428631613533 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43337059035 / 1000000000000) (-43337058976 / 1000000000000), orderedInterval (-3367548129 / 1000000000000) (-3367548069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (843158274546399 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48665989646 / 1000000000000) (-48665989645 / 1000000000000), orderedInterval (-25414623402 / 1000000000000) (-25414623401 / 1000000000000)))) (orderedInterval (3527821615 / 1000000000000) (3527826282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (453453324268833 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65013745995 / 1000000000000) (65013745996 / 1000000000000), orderedInterval (36981635599 / 1000000000000) (36981635600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1231213984625499 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29727177438 / 1000000000000) (29727177439 / 1000000000000), orderedInterval (34369180091 / 1000000000000) (34369180092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1681117436284923 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3538532366 / 1000000000000) (3538532367 / 1000000000000), orderedInterval (38754449704 / 1000000000000) (38754449705 / 1000000000000)))) (orderedInterval (853303871 / 1000000000000) (853303913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (710841725453601 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32582799142 / 1000000000000) (32582806293 / 1000000000000), orderedInterval (-50298349711 / 1000000000000) (-50298342560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2889532149216321 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16809949186 / 1000000000000) (16809949187 / 1000000000000), orderedInterval (24456772808 / 1000000000000) (24456772809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1930073563014639 / 4000000000000) 2 (IntervalRat.scale (777 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17469626501 / 1000000000000) (-17469625955 / 1000000000000), orderedInterval (31864318176 / 1000000000000) (31864318723 / 1000000000000)))) (orderedInterval (-337288386 / 1000000000000) (-337287995 / 1000000000000))) = true
  rfl'

theorem compactCertificate517_chunkChecks2 :
    compactCertificate517.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate517.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate517_chunkChecks2_0
    compactCertificate517_chunkChecks2_1 compactCertificate517_chunkChecks2_2

theorem compactCertificate517_chunkChecks3_0 :
    compactCertificate517.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (777 / 2) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10891479070 / 1000000000000) (-10891479024 / 1000000000000), orderedInterval (39001679163 / 1000000000000) (39001679209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1144669366519077 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41314434320 / 1000000000000) (-41314434319 / 1000000000000), orderedInterval (-22682095352 / 1000000000000) (-22682095351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (370162554415941 / 800000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36894590519 / 1000000000000) (-36894589064 / 1000000000000), orderedInterval (3868597285 / 1000000000000) (3868598740 / 1000000000000)))) (orderedInterval (-15777298510 / 1000000000000) (-15777298306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (334011666304239 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44605290995 / 1000000000000) (44605298715 / 1000000000000), orderedInterval (-75329426837 / 1000000000000) (-75329419116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2436078824946711 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10657782594 / 1000000000000) (10657782595 / 1000000000000), orderedInterval (30515515569 / 1000000000000) (30515515570 / 1000000000000)))) (orderedInterval (8175001258 / 1000000000000) (8175001494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1794404636641743 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5201890166 / 1000000000000) (-5201890165 / 1000000000000), orderedInterval (-37304565044 / 1000000000000) (-37304565043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3074742929532939 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6258719016 / 1000000000000) (6258719018 / 1000000000000), orderedInterval (-28093590681 / 1000000000000) (-28093590679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2264841725453601 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33467203309 / 1000000000000) (33467203678 / 1000000000000), orderedInterval (2043548074 / 1000000000000) (2043548443 / 1000000000000)))) (orderedInterval (-6862382846 / 1000000000000) (-6862382695 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate517_chunkChecks3_1 :
    compactCertificate517.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3474849637034223 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17921261431 / 1000000000000) (17921262183 / 1000000000000), orderedInterval (-20299717308 / 1000000000000) (-20299716555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2006205373334967 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11150725517 / 1000000000000) (-11150725478 / 1000000000000), orderedInterval (33848420006 / 1000000000000) (33848420045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3560046640524003 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26422698185 / 1000000000000) (-26422674597 / 1000000000000), orderedInterval (4154308513 / 1000000000000) (4154332101 / 1000000000000)))) (orderedInterval (-52919225958 / 1000000000000) (-52919182595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3326257368681807 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4748248616 / 1000000000000) (4748248617 / 1000000000000), orderedInterval (-27261305692 / 1000000000000) (-27261305691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2373774209986431 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14766987415 / 1000000000000) (-14766987414 / 1000000000000), orderedInterval (-29222669027 / 1000000000000) (-29222669026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2691606954961449 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30235424852 / 1000000000000) (30235425000 / 1000000000000), orderedInterval (5625556726 / 1000000000000) (5625556874 / 1000000000000)))) (orderedInterval (5160331115 / 1000000000000) (5160331330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2243981264915481 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18024900668 / 1000000000000) (18024901394 / 1000000000000), orderedInterval (-28474934241 / 1000000000000) (-28474933514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1982625500677101 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2502422391 / 1000000000000) (2502422392 / 1000000000000), orderedInterval (35748502980 / 1000000000000) (35748502981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (574642146636999 / 800000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9838505321 / 1000000000000) (9838505331 / 1000000000000), orderedInterval (-28104667213 / 1000000000000) (-28104667203 / 1000000000000)))) (orderedInterval (9789286053 / 1000000000000) (9789286204 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate517_chunkChecks3_2 :
    compactCertificate517.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1589490419357253 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29389461271 / 1000000000000) (29389488572 / 1000000000000), orderedInterval (-27209244770 / 1000000000000) (-27209217470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1347428631613533 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43337059035 / 1000000000000) (-43337058976 / 1000000000000), orderedInterval (-3367548129 / 1000000000000) (-3367548069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (843158274546399 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48665989646 / 1000000000000) (-48665989645 / 1000000000000), orderedInterval (-25414623402 / 1000000000000) (-25414623401 / 1000000000000)))) (orderedInterval (-4656635807 / 1000000000000) (-4656631038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (453453324268833 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65013745995 / 1000000000000) (65013745996 / 1000000000000), orderedInterval (36981635599 / 1000000000000) (36981635600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1231213984625499 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29727177438 / 1000000000000) (29727177439 / 1000000000000), orderedInterval (34369180091 / 1000000000000) (34369180092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1681117436284923 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3538532366 / 1000000000000) (3538532367 / 1000000000000), orderedInterval (38754449704 / 1000000000000) (38754449705 / 1000000000000)))) (orderedInterval (4162735400 / 1000000000000) (4162735444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (710841725453601 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32582799142 / 1000000000000) (32582806293 / 1000000000000), orderedInterval (-50298349711 / 1000000000000) (-50298342560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2889532149216321 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16809949186 / 1000000000000) (16809949187 / 1000000000000), orderedInterval (24456772808 / 1000000000000) (24456772809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1930073563014639 / 4000000000000) 3 (IntervalRat.scale (777 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17469626501 / 1000000000000) (-17469625955 / 1000000000000), orderedInterval (31864318176 / 1000000000000) (31864318723 / 1000000000000)))) (orderedInterval (24282688005 / 1000000000000) (24282688551 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate517_chunkChecks3 :
    compactCertificate517.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate517.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate517_chunkChecks3_0
    compactCertificate517_chunkChecks3_1 compactCertificate517_chunkChecks3_2

theorem compactCertificate517_chunkChecks4_0 :
    compactCertificate517.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (777 / 2) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-10891479070 / 1000000000000) (-10891479024 / 1000000000000), orderedInterval (39001679163 / 1000000000000) (39001679209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1144669366519077 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41314434320 / 1000000000000) (-41314434319 / 1000000000000), orderedInterval (-22682095352 / 1000000000000) (-22682095351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (370162554415941 / 800000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36894590519 / 1000000000000) (-36894589064 / 1000000000000), orderedInterval (3868597285 / 1000000000000) (3868598740 / 1000000000000)))) (orderedInterval (-8705252447 / 1000000000000) (-8705252208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (334011666304239 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44605290995 / 1000000000000) (44605298715 / 1000000000000), orderedInterval (-75329426837 / 1000000000000) (-75329419116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (897202318320483 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47700684772 / 1000000000000) (-47700667185 / 1000000000000), orderedInterval (23831524538 / 1000000000000) (23831542125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2436078824946711 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10657782594 / 1000000000000) (10657782595 / 1000000000000), orderedInterval (30515515569 / 1000000000000) (30515515570 / 1000000000000)))) (orderedInterval (-4812073361 / 1000000000000) (-4812073119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1794404636641743 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5201890166 / 1000000000000) (-5201890165 / 1000000000000), orderedInterval (-37304565044 / 1000000000000) (-37304565043 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3074742929532939 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6258719016 / 1000000000000) (6258719018 / 1000000000000), orderedInterval (-28093590681 / 1000000000000) (-28093590679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2264841725453601 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33467203309 / 1000000000000) (33467203678 / 1000000000000), orderedInterval (2043548074 / 1000000000000) (2043548443 / 1000000000000)))) (orderedInterval (726000310 / 1000000000000) (726000578 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate517_chunkChecks4_1 :
    compactCertificate517.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3474849637034223 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17921261431 / 1000000000000) (17921262183 / 1000000000000), orderedInterval (-20299717308 / 1000000000000) (-20299716555 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2006205373334967 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11150725517 / 1000000000000) (-11150725478 / 1000000000000), orderedInterval (33848420006 / 1000000000000) (33848420045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3560046640524003 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26422698185 / 1000000000000) (-26422674597 / 1000000000000), orderedInterval (4154308513 / 1000000000000) (4154332101 / 1000000000000)))) (orderedInterval (-185089262861 / 1000000000000) (-185089163611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3326257368681807 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4748248616 / 1000000000000) (4748248617 / 1000000000000), orderedInterval (-27261305692 / 1000000000000) (-27261305691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2373774209986431 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14766987415 / 1000000000000) (-14766987414 / 1000000000000), orderedInterval (-29222669027 / 1000000000000) (-29222669026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2691606954961449 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30235424852 / 1000000000000) (30235425000 / 1000000000000), orderedInterval (5625556726 / 1000000000000) (5625556874 / 1000000000000)))) (orderedInterval (-10805588321 / 1000000000000) (-10805587947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2243981264915481 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18024900668 / 1000000000000) (18024901394 / 1000000000000), orderedInterval (-28474934241 / 1000000000000) (-28474933514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1982625500677101 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2502422391 / 1000000000000) (2502422392 / 1000000000000), orderedInterval (35748502980 / 1000000000000) (35748502981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (574642146636999 / 800000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9838505321 / 1000000000000) (9838505331 / 1000000000000), orderedInterval (-28104667213 / 1000000000000) (-28104667203 / 1000000000000)))) (orderedInterval (3418919122 / 1000000000000) (3418919357 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate517_chunkChecks4_2 :
    compactCertificate517.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1589490419357253 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29389461271 / 1000000000000) (29389488572 / 1000000000000), orderedInterval (-27209244770 / 1000000000000) (-27209217470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1347428631613533 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43337059035 / 1000000000000) (-43337058976 / 1000000000000), orderedInterval (-3367548129 / 1000000000000) (-3367548069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (843158274546399 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48665989646 / 1000000000000) (-48665989645 / 1000000000000), orderedInterval (-25414623402 / 1000000000000) (-25414623401 / 1000000000000)))) (orderedInterval (-3870255550 / 1000000000000) (-3870250664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (453453324268833 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65013745995 / 1000000000000) (65013745996 / 1000000000000), orderedInterval (36981635599 / 1000000000000) (36981635600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1231213984625499 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29727177438 / 1000000000000) (29727177439 / 1000000000000), orderedInterval (34369180091 / 1000000000000) (34369180092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1681117436284923 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3538532366 / 1000000000000) (3538532367 / 1000000000000), orderedInterval (38754449704 / 1000000000000) (38754449705 / 1000000000000)))) (orderedInterval (-667283993 / 1000000000000) (-667283947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (710841725453601 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32582799142 / 1000000000000) (32582806293 / 1000000000000), orderedInterval (-50298349711 / 1000000000000) (-50298342560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2889532149216321 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16809949186 / 1000000000000) (16809949187 / 1000000000000), orderedInterval (24456772808 / 1000000000000) (24456772809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1930073563014639 / 4000000000000) 4 (IntervalRat.scale (777 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17469626501 / 1000000000000) (-17469625955 / 1000000000000), orderedInterval (31864318176 / 1000000000000) (31864318723 / 1000000000000)))) (orderedInterval (-8673967417 / 1000000000000) (-8673966617 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate517_chunkChecks4 :
    compactCertificate517.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate517.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate517_chunkChecks4_0
    compactCertificate517_chunkChecks4_1 compactCertificate517_chunkChecks4_2

theorem compactCertificate517_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate517.chunkCheck r b = true :=
  compactCertificate517.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate517_chunkChecks0
    · exact compactCertificate517_chunkChecks1
    · exact compactCertificate517_chunkChecks2
    · exact compactCertificate517_chunkChecks3
    · exact compactCertificate517_chunkChecks4)

theorem compactCertificate517_coefficient0 :
    compactCertificate517.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate517_coefficient1 :
    compactCertificate517.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate517_coefficient2 :
    compactCertificate517.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate517_coefficient3 :
    compactCertificate517.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate517_coefficient4 :
    compactCertificate517.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate517_coefficients : ∀ r : Fin 5,
    compactCertificate517.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate517_coefficient0
  · exact compactCertificate517_coefficient1
  · exact compactCertificate517_coefficient2
  · exact compactCertificate517_coefficient3
  · exact compactCertificate517_coefficient4

theorem compactCertificate517_lower : (1 : ℚ) ≤ compactCertificate517.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate517, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate517_proves {t : ℝ} (ht : t ∈ compactCertificate517.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate517.proves compactCertificate517_states compactCertificate517_chunks
    compactCertificate517_coefficients compactCertificate517_lower ht

end Erdos232
