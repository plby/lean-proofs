/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate619 : CompactCertificate where
  left := 490
  right := 491
  center := 981 / 2
  grid := fun i =>
    match i.val with
    | 0 => 156
    | 1 => 115
    | 2 => 186
    | 3 => 34
    | 4 => 90
    | 5 => 245
    | 6 => 180
    | 7 => 309
    | 8 => 228
    | 9 => 349
    | 10 => 202
    | 11 => 358
    | 12 => 334
    | 13 => 239
    | 14 => 271
    | 15 => 226
    | 16 => 199
    | 17 => 289
    | 18 => 160
    | 19 => 135
    | 20 => 85
    | 21 => 46
    | 22 => 124
    | 23 => 169
    | 24 => 71
    | 25 => 290
    | _ => 194
  point := fun i =>
    match i.val with
    | 0 => 981 / 2
    | 1 => 1445200319890881 / 4000000000000
    | 2 => 467348089938273 / 800000000000
    | 3 => 421705848963267 / 4000000000000
    | 4 => 1132761228149799 / 4000000000000
    | 5 => 3075667087867083 / 4000000000000
    | 6 => 2265522456300579 / 4000000000000
    | 7 => 3882011343464367 / 4000000000000
    | 8 => 2859471985418253 / 4000000000000
    | 9 => 4387165371854019 / 4000000000000
    | 10 => 2532931108419051 / 4000000000000
    | 11 => 4494730700584359 / 4000000000000
    | 12 => 4199560461617571 / 4000000000000
    | 13 => 2997004504500243 / 4000000000000
    | 14 => 3398283684449397 / 4000000000000
    | 15 => 2833134647209893 / 4000000000000
    | 16 => 2503160381163753 / 4000000000000
    | 17 => 725513443823547 / 800000000000
    | 18 => 2006808367296609 / 4000000000000
    | 19 => 1701193677751449 / 4000000000000
    | 20 => 1064528014581747 / 4000000000000
    | 21 => 572506706702349 / 4000000000000
    | 22 => 1554467077114047 / 4000000000000
    | 23 => 2122491898321119 / 4000000000000
    | 24 => 897471985418253 / 4000000000000
    | 25 => 3648173794570413 / 4000000000000
    | _ => 2436811023574467 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (33534577719 / 1000000000000) (33534577721 / 1000000000000), orderedInterval (13131348260 / 1000000000000) (13131348262 / 1000000000000))
    | 1 => (orderedInterval (-30169829338 / 1000000000000) (-30169829337 / 1000000000000), orderedInterval (-29143969810 / 1000000000000) (-29143969809 / 1000000000000))
    | 2 => (orderedInterval (19556746460 / 1000000000000) (19556746461 / 1000000000000), orderedInterval (26578199259 / 1000000000000) (26578199260 / 1000000000000))
    | 3 => (orderedInterval (-44099577772 / 1000000000000) (-44099564225 / 1000000000000), orderedInterval (64191725701 / 1000000000000) (64191739248 / 1000000000000))
    | 4 => (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))
    | 5 => (orderedInterval (-339739311 / 1000000000000) (-339739310 / 1000000000000), orderedInterval (-28771786656 / 1000000000000) (-28771786655 / 1000000000000))
    | 6 => (orderedInterval (33329826142 / 1000000000000) (33329828924 / 1000000000000), orderedInterval (-3653817813 / 1000000000000) (-3653815031 / 1000000000000))
    | 7 => (orderedInterval (-13079474669 / 1000000000000) (-13079474668 / 1000000000000), orderedInterval (-22013624384 / 1000000000000) (-22013624383 / 1000000000000))
    | 8 => (orderedInterval (-17578941763 / 1000000000000) (-17578941141 / 1000000000000), orderedInterval (24127074617 / 1000000000000) (24127075239 / 1000000000000))
    | 9 => (orderedInterval (-22095487714 / 1000000000000) (-22095487585 / 1000000000000), orderedInterval (-9593455173 / 1000000000000) (-9593455044 / 1000000000000))
    | 10 => (orderedInterval (-17475342623 / 1000000000000) (-17475342037 / 1000000000000), orderedInterval (26470579374 / 1000000000000) (26470579960 / 1000000000000))
    | 11 => (orderedInterval (-5245632301 / 1000000000000) (-5245632300 / 1000000000000), orderedInterval (23219376067 / 1000000000000) (23219376068 / 1000000000000))
    | 12 => (orderedInterval (24193648742 / 1000000000000) (24193650318 / 1000000000000), orderedInterval (4574898523 / 1000000000000) (4574900100 / 1000000000000))
    | 13 => (orderedInterval (20997203189 / 1000000000000) (20997206972 / 1000000000000), orderedInterval (-20232622543 / 1000000000000) (-20232618760 / 1000000000000))
    | 14 => (orderedInterval (23260083930 / 1000000000000) (23260103000 / 1000000000000), orderedInterval (-14446671032 / 1000000000000) (-14446651962 / 1000000000000))
    | 15 => (orderedInterval (-24051755465 / 1000000000000) (-24051738578 / 1000000000000), orderedInterval (17914840191 / 1000000000000) (17914857078 / 1000000000000))
    | 16 => (orderedInterval (-31422182660 / 1000000000000) (-31422182534 / 1000000000000), orderedInterval (-5447712498 / 1000000000000) (-5447712372 / 1000000000000))
    | 17 => (orderedInterval (6380531486 / 1000000000000) (6380531487 / 1000000000000), orderedInterval (-25718664340 / 1000000000000) (-25718664338 / 1000000000000))
    | 18 => (orderedInterval (-5941746992 / 1000000000000) (-5941746988 / 1000000000000), orderedInterval (35128793703 / 1000000000000) (35128793707 / 1000000000000))
    | 19 => (orderedInterval (-35669665897 / 1000000000000) (-35669640775 / 1000000000000), orderedInterval (15027011297 / 1000000000000) (15027036419 / 1000000000000))
    | 20 => (orderedInterval (5779445880 / 1000000000000) (5779445891 / 1000000000000), orderedInterval (-48577538382 / 1000000000000) (-48577538370 / 1000000000000))
    | 21 => (orderedInterval (-37770889734 / 1000000000000) (-37770878627 / 1000000000000), orderedInterval (55098443542 / 1000000000000) (55098454650 / 1000000000000))
    | 22 => (orderedInterval (-6274144997 / 1000000000000) (-6274144989 / 1000000000000), orderedInterval (39993131510 / 1000000000000) (39993131517 / 1000000000000))
    | 23 => (orderedInterval (-15963505387 / 1000000000000) (-15963505386 / 1000000000000), orderedInterval (-30724605775 / 1000000000000) (-30724605774 / 1000000000000))
    | 24 => (orderedInterval (-45987156641 / 1000000000000) (-45987123664 / 1000000000000), orderedInterval (26983137245 / 1000000000000) (26983170223 / 1000000000000))
    | 25 => (orderedInterval (25913869200 / 1000000000000) (25913907129 / 1000000000000), orderedInterval (-5160585288 / 1000000000000) (-5160547359 / 1000000000000))
    | _ => (orderedInterval (16033620234 / 1000000000000) (16033620235 / 1000000000000), orderedInterval (28056894807 / 1000000000000) (28056894808 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14158420543 / 1000000000000) (14158420578 / 1000000000000)
      | 1 => orderedInterval (2135295318 / 1000000000000) (2135295524 / 1000000000000)
      | 2 => orderedInterval (-21425023 / 1000000000000) (-21424980 / 1000000000000)
      | 3 => orderedInterval (1885624643 / 1000000000000) (1885624904 / 1000000000000)
      | 4 => orderedInterval (1431076113 / 1000000000000) (1431076655 / 1000000000000)
      | 5 => orderedInterval (1683812141 / 1000000000000) (1683812391 / 1000000000000)
      | 6 => orderedInterval (3157091899 / 1000000000000) (3157093445 / 1000000000000)
      | 7 => orderedInterval (2063209339 / 1000000000000) (2063209603 / 1000000000000)
      | _ => orderedInterval (-5394996301 / 1000000000000) (-5394992879 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6862301855 / 1000000000000) (6862301895 / 1000000000000)
      | 1 => orderedInterval (3387264302 / 1000000000000) (3387264401 / 1000000000000)
      | 2 => orderedInterval (2193276761 / 1000000000000) (2193276831 / 1000000000000)
      | 3 => orderedInterval (13905369971 / 1000000000000) (13905370481 / 1000000000000)
      | 4 => orderedInterval (-2972699503 / 1000000000000) (-2972698634 / 1000000000000)
      | 5 => orderedInterval (-521037544 / 1000000000000) (-521037185 / 1000000000000)
      | 6 => orderedInterval (-7340630691 / 1000000000000) (-7340629344 / 1000000000000)
      | 7 => orderedInterval (1531582404 / 1000000000000) (1531582517 / 1000000000000)
      | _ => orderedInterval (-5682671646 / 1000000000000) (-5682665623 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14781256602 / 1000000000000) (-14781256557 / 1000000000000)
      | 1 => orderedInterval (-632592191 / 1000000000000) (-632592091 / 1000000000000)
      | 2 => orderedInterval (-681397398 / 1000000000000) (-681397280 / 1000000000000)
      | 3 => orderedInterval (-13587331135 / 1000000000000) (-13587330083 / 1000000000000)
      | 4 => orderedInterval (-2272704451 / 1000000000000) (-2272703038 / 1000000000000)
      | 5 => orderedInterval (-2905214941 / 1000000000000) (-2905214420 / 1000000000000)
      | 6 => orderedInterval (-2552188981 / 1000000000000) (-2552187800 / 1000000000000)
      | 7 => orderedInterval (-1583620798 / 1000000000000) (-1583620727 / 1000000000000)
      | _ => orderedInterval (12003381740 / 1000000000000) (12003392750 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-7700976191 / 1000000000000) (-7700976138 / 1000000000000)
      | 1 => orderedInterval (-7981393589 / 1000000000000) (-7981393448 / 1000000000000)
      | 2 => orderedInterval (-7063116465 / 1000000000000) (-7063116263 / 1000000000000)
      | 3 => orderedInterval (-62935930670 / 1000000000000) (-62935928426 / 1000000000000)
      | 4 => orderedInterval (7253938303 / 1000000000000) (7253940627 / 1000000000000)
      | 5 => orderedInterval (2897641729 / 1000000000000) (2897642488 / 1000000000000)
      | 6 => orderedInterval (6822726939 / 1000000000000) (6822727974 / 1000000000000)
      | 7 => orderedInterval (-2501347516 / 1000000000000) (-2501347456 / 1000000000000)
      | _ => orderedInterval (7344937363 / 1000000000000) (7344957688 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15549603745 / 1000000000000) (15549603806 / 1000000000000)
      | 1 => orderedInterval (360825098 / 1000000000000) (360825313 / 1000000000000)
      | 2 => orderedInterval (4294876469 / 1000000000000) (4294876824 / 1000000000000)
      | 3 => orderedInterval (74273386611 / 1000000000000) (74273391512 / 1000000000000)
      | 4 => orderedInterval (553325651 / 1000000000000) (553329534 / 1000000000000)
      | 5 => orderedInterval (5453941849 / 1000000000000) (5453942965 / 1000000000000)
      | 6 => orderedInterval (2169449903 / 1000000000000) (2169450815 / 1000000000000)
      | 7 => orderedInterval (1746916790 / 1000000000000) (1746916849 / 1000000000000)
      | _ => orderedInterval (-32416263001 / 1000000000000) (-32416225306 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21098108672 / 1000000000000) (21098115241 / 1000000000000)
    | 1 => orderedInterval (11362755909 / 1000000000000) (11362765339 / 1000000000000)
    | 2 => orderedInterval (-26992924757 / 1000000000000) (-26992909246 / 1000000000000)
    | 3 => orderedInterval (-63863520097 / 1000000000000) (-63863492954 / 1000000000000)
    | _ => orderedInterval (71986063115 / 1000000000000) (71986112312 / 1000000000000)

theorem compactCertificate619_stateChecks0 :
    compactCertificate619.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (981 / 2)) (orderedInterval (33534577719 / 1000000000000) (33534577721 / 1000000000000), orderedInterval (13131348260 / 1000000000000) (13131348262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1445200319890881 / 4000000000000)) (orderedInterval (-30169829338 / 1000000000000) (-30169829337 / 1000000000000), orderedInterval (-29143969810 / 1000000000000) (-29143969809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (467348089938273 / 800000000000)) (orderedInterval (19556746460 / 1000000000000) (19556746461 / 1000000000000), orderedInterval (26578199259 / 1000000000000) (26578199260 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_stateChecks1 :
    compactCertificate619.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (421705848963267 / 4000000000000)) (orderedInterval (-44099577772 / 1000000000000) (-44099564225 / 1000000000000), orderedInterval (64191725701 / 1000000000000) (64191739248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1132761228149799 / 4000000000000)) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3075667087867083 / 4000000000000)) (orderedInterval (-339739311 / 1000000000000) (-339739310 / 1000000000000), orderedInterval (-28771786656 / 1000000000000) (-28771786655 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_stateChecks2 :
    compactCertificate619.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2265522456300579 / 4000000000000)) (orderedInterval (33329826142 / 1000000000000) (33329828924 / 1000000000000), orderedInterval (-3653817813 / 1000000000000) (-3653815031 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 309 12 (3882011343464367 / 4000000000000)) (orderedInterval (-13079474669 / 1000000000000) (-13079474668 / 1000000000000), orderedInterval (-22013624384 / 1000000000000) (-22013624383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2859471985418253 / 4000000000000)) (orderedInterval (-17578941763 / 1000000000000) (-17578941141 / 1000000000000), orderedInterval (24127074617 / 1000000000000) (24127075239 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_stateChecks3 :
    compactCertificate619.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 349 12 (4387165371854019 / 4000000000000)) (orderedInterval (-22095487714 / 1000000000000) (-22095487585 / 1000000000000), orderedInterval (-9593455173 / 1000000000000) (-9593455044 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2532931108419051 / 4000000000000)) (orderedInterval (-17475342623 / 1000000000000) (-17475342037 / 1000000000000), orderedInterval (26470579374 / 1000000000000) (26470579960 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 358 12 (4494730700584359 / 4000000000000)) (orderedInterval (-5245632301 / 1000000000000) (-5245632300 / 1000000000000), orderedInterval (23219376067 / 1000000000000) (23219376068 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_stateChecks4 :
    compactCertificate619.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 334 12 (4199560461617571 / 4000000000000)) (orderedInterval (24193648742 / 1000000000000) (24193650318 / 1000000000000), orderedInterval (4574898523 / 1000000000000) (4574900100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (2997004504500243 / 4000000000000)) (orderedInterval (20997203189 / 1000000000000) (20997206972 / 1000000000000), orderedInterval (-20232622543 / 1000000000000) (-20232618760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (3398283684449397 / 4000000000000)) (orderedInterval (23260083930 / 1000000000000) (23260103000 / 1000000000000), orderedInterval (-14446671032 / 1000000000000) (-14446651962 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_stateChecks5 :
    compactCertificate619.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2833134647209893 / 4000000000000)) (orderedInterval (-24051755465 / 1000000000000) (-24051738578 / 1000000000000), orderedInterval (17914840191 / 1000000000000) (17914857078 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2503160381163753 / 4000000000000)) (orderedInterval (-31422182660 / 1000000000000) (-31422182534 / 1000000000000), orderedInterval (-5447712498 / 1000000000000) (-5447712372 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (725513443823547 / 800000000000)) (orderedInterval (6380531486 / 1000000000000) (6380531487 / 1000000000000), orderedInterval (-25718664340 / 1000000000000) (-25718664338 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_stateChecks6 :
    compactCertificate619.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2006808367296609 / 4000000000000)) (orderedInterval (-5941746992 / 1000000000000) (-5941746988 / 1000000000000), orderedInterval (35128793703 / 1000000000000) (35128793707 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1701193677751449 / 4000000000000)) (orderedInterval (-35669665897 / 1000000000000) (-35669640775 / 1000000000000), orderedInterval (15027011297 / 1000000000000) (15027036419 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1064528014581747 / 4000000000000)) (orderedInterval (5779445880 / 1000000000000) (5779445891 / 1000000000000), orderedInterval (-48577538382 / 1000000000000) (-48577538370 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_stateChecks7 :
    compactCertificate619.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (572506706702349 / 4000000000000)) (orderedInterval (-37770889734 / 1000000000000) (-37770878627 / 1000000000000), orderedInterval (55098443542 / 1000000000000) (55098454650 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1554467077114047 / 4000000000000)) (orderedInterval (-6274144997 / 1000000000000) (-6274144989 / 1000000000000), orderedInterval (39993131510 / 1000000000000) (39993131517 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2122491898321119 / 4000000000000)) (orderedInterval (-15963505387 / 1000000000000) (-15963505386 / 1000000000000), orderedInterval (-30724605775 / 1000000000000) (-30724605774 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_stateChecks8 :
    compactCertificate619.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (897471985418253 / 4000000000000)) (orderedInterval (-45987156641 / 1000000000000) (-45987123664 / 1000000000000), orderedInterval (26983137245 / 1000000000000) (26983170223 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 290 12 (3648173794570413 / 4000000000000)) (orderedInterval (25913869200 / 1000000000000) (25913907129 / 1000000000000), orderedInterval (-5160585288 / 1000000000000) (-5160547359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2436811023574467 / 4000000000000)) (orderedInterval (16033620234 / 1000000000000) (16033620235 / 1000000000000), orderedInterval (28056894807 / 1000000000000) (28056894808 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_states : ∀ j,
    BesselStateValid (compactCertificate619.point j) (compactCertificate619.state j) :=
  compactCertificate619.statesValid_of_checks3 compactCertificate619_stateChecks0
    compactCertificate619_stateChecks1 compactCertificate619_stateChecks2
    compactCertificate619_stateChecks3 compactCertificate619_stateChecks4
    compactCertificate619_stateChecks5 compactCertificate619_stateChecks6
    compactCertificate619_stateChecks7 compactCertificate619_stateChecks8

theorem compactCertificate619_chunkChecks0_0 :
    compactCertificate619.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (981 / 2) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33534577719 / 1000000000000) (33534577721 / 1000000000000), orderedInterval (13131348260 / 1000000000000) (13131348262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1445200319890881 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30169829338 / 1000000000000) (-30169829337 / 1000000000000), orderedInterval (-29143969810 / 1000000000000) (-29143969809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (467348089938273 / 800000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19556746460 / 1000000000000) (19556746461 / 1000000000000), orderedInterval (26578199259 / 1000000000000) (26578199260 / 1000000000000)))) (orderedInterval (14158420543 / 1000000000000) (14158420578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (421705848963267 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44099577772 / 1000000000000) (-44099564225 / 1000000000000), orderedInterval (64191725701 / 1000000000000) (64191739248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3075667087867083 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-339739311 / 1000000000000) (-339739310 / 1000000000000), orderedInterval (-28771786656 / 1000000000000) (-28771786655 / 1000000000000)))) (orderedInterval (2135295318 / 1000000000000) (2135295524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2265522456300579 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33329826142 / 1000000000000) (33329828924 / 1000000000000), orderedInterval (-3653817813 / 1000000000000) (-3653815031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3882011343464367 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13079474669 / 1000000000000) (-13079474668 / 1000000000000), orderedInterval (-22013624384 / 1000000000000) (-22013624383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2859471985418253 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17578941763 / 1000000000000) (-17578941141 / 1000000000000), orderedInterval (24127074617 / 1000000000000) (24127075239 / 1000000000000)))) (orderedInterval (-21425023 / 1000000000000) (-21424980 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks0_1 :
    compactCertificate619.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4387165371854019 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22095487714 / 1000000000000) (-22095487585 / 1000000000000), orderedInterval (-9593455173 / 1000000000000) (-9593455044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2532931108419051 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17475342623 / 1000000000000) (-17475342037 / 1000000000000), orderedInterval (26470579374 / 1000000000000) (26470579960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4494730700584359 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5245632301 / 1000000000000) (-5245632300 / 1000000000000), orderedInterval (23219376067 / 1000000000000) (23219376068 / 1000000000000)))) (orderedInterval (1885624643 / 1000000000000) (1885624904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4199560461617571 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24193648742 / 1000000000000) (24193650318 / 1000000000000), orderedInterval (4574898523 / 1000000000000) (4574900100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2997004504500243 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20997203189 / 1000000000000) (20997206972 / 1000000000000), orderedInterval (-20232622543 / 1000000000000) (-20232618760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3398283684449397 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23260083930 / 1000000000000) (23260103000 / 1000000000000), orderedInterval (-14446671032 / 1000000000000) (-14446651962 / 1000000000000)))) (orderedInterval (1431076113 / 1000000000000) (1431076655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2833134647209893 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24051755465 / 1000000000000) (-24051738578 / 1000000000000), orderedInterval (17914840191 / 1000000000000) (17914857078 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2503160381163753 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31422182660 / 1000000000000) (-31422182534 / 1000000000000), orderedInterval (-5447712498 / 1000000000000) (-5447712372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (725513443823547 / 800000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6380531486 / 1000000000000) (6380531487 / 1000000000000), orderedInterval (-25718664340 / 1000000000000) (-25718664338 / 1000000000000)))) (orderedInterval (1683812141 / 1000000000000) (1683812391 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks0_2 :
    compactCertificate619.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2006808367296609 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-5941746992 / 1000000000000) (-5941746988 / 1000000000000), orderedInterval (35128793703 / 1000000000000) (35128793707 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1701193677751449 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35669665897 / 1000000000000) (-35669640775 / 1000000000000), orderedInterval (15027011297 / 1000000000000) (15027036419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1064528014581747 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5779445880 / 1000000000000) (5779445891 / 1000000000000), orderedInterval (-48577538382 / 1000000000000) (-48577538370 / 1000000000000)))) (orderedInterval (3157091899 / 1000000000000) (3157093445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (572506706702349 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37770889734 / 1000000000000) (-37770878627 / 1000000000000), orderedInterval (55098443542 / 1000000000000) (55098454650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1554467077114047 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6274144997 / 1000000000000) (-6274144989 / 1000000000000), orderedInterval (39993131510 / 1000000000000) (39993131517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2122491898321119 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15963505387 / 1000000000000) (-15963505386 / 1000000000000), orderedInterval (-30724605775 / 1000000000000) (-30724605774 / 1000000000000)))) (orderedInterval (2063209339 / 1000000000000) (2063209603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (897471985418253 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45987156641 / 1000000000000) (-45987123664 / 1000000000000), orderedInterval (26983137245 / 1000000000000) (26983170223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3648173794570413 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25913869200 / 1000000000000) (25913907129 / 1000000000000), orderedInterval (-5160585288 / 1000000000000) (-5160547359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2436811023574467 / 4000000000000) 0 (IntervalRat.scale (981 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16033620234 / 1000000000000) (16033620235 / 1000000000000), orderedInterval (28056894807 / 1000000000000) (28056894808 / 1000000000000)))) (orderedInterval (-5394996301 / 1000000000000) (-5394992879 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks0 :
    compactCertificate619.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate619.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate619_chunkChecks0_0
    compactCertificate619_chunkChecks0_1 compactCertificate619_chunkChecks0_2

theorem compactCertificate619_chunkChecks1_0 :
    compactCertificate619.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (981 / 2) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33534577719 / 1000000000000) (33534577721 / 1000000000000), orderedInterval (13131348260 / 1000000000000) (13131348262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1445200319890881 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30169829338 / 1000000000000) (-30169829337 / 1000000000000), orderedInterval (-29143969810 / 1000000000000) (-29143969809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (467348089938273 / 800000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19556746460 / 1000000000000) (19556746461 / 1000000000000), orderedInterval (26578199259 / 1000000000000) (26578199260 / 1000000000000)))) (orderedInterval (6862301855 / 1000000000000) (6862301895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (421705848963267 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44099577772 / 1000000000000) (-44099564225 / 1000000000000), orderedInterval (64191725701 / 1000000000000) (64191739248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3075667087867083 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-339739311 / 1000000000000) (-339739310 / 1000000000000), orderedInterval (-28771786656 / 1000000000000) (-28771786655 / 1000000000000)))) (orderedInterval (3387264302 / 1000000000000) (3387264401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2265522456300579 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33329826142 / 1000000000000) (33329828924 / 1000000000000), orderedInterval (-3653817813 / 1000000000000) (-3653815031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3882011343464367 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13079474669 / 1000000000000) (-13079474668 / 1000000000000), orderedInterval (-22013624384 / 1000000000000) (-22013624383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2859471985418253 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17578941763 / 1000000000000) (-17578941141 / 1000000000000), orderedInterval (24127074617 / 1000000000000) (24127075239 / 1000000000000)))) (orderedInterval (2193276761 / 1000000000000) (2193276831 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks1_1 :
    compactCertificate619.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4387165371854019 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22095487714 / 1000000000000) (-22095487585 / 1000000000000), orderedInterval (-9593455173 / 1000000000000) (-9593455044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2532931108419051 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17475342623 / 1000000000000) (-17475342037 / 1000000000000), orderedInterval (26470579374 / 1000000000000) (26470579960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4494730700584359 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5245632301 / 1000000000000) (-5245632300 / 1000000000000), orderedInterval (23219376067 / 1000000000000) (23219376068 / 1000000000000)))) (orderedInterval (13905369971 / 1000000000000) (13905370481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4199560461617571 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24193648742 / 1000000000000) (24193650318 / 1000000000000), orderedInterval (4574898523 / 1000000000000) (4574900100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2997004504500243 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20997203189 / 1000000000000) (20997206972 / 1000000000000), orderedInterval (-20232622543 / 1000000000000) (-20232618760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3398283684449397 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23260083930 / 1000000000000) (23260103000 / 1000000000000), orderedInterval (-14446671032 / 1000000000000) (-14446651962 / 1000000000000)))) (orderedInterval (-2972699503 / 1000000000000) (-2972698634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2833134647209893 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24051755465 / 1000000000000) (-24051738578 / 1000000000000), orderedInterval (17914840191 / 1000000000000) (17914857078 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2503160381163753 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31422182660 / 1000000000000) (-31422182534 / 1000000000000), orderedInterval (-5447712498 / 1000000000000) (-5447712372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (725513443823547 / 800000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6380531486 / 1000000000000) (6380531487 / 1000000000000), orderedInterval (-25718664340 / 1000000000000) (-25718664338 / 1000000000000)))) (orderedInterval (-521037544 / 1000000000000) (-521037185 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks1_2 :
    compactCertificate619.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2006808367296609 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-5941746992 / 1000000000000) (-5941746988 / 1000000000000), orderedInterval (35128793703 / 1000000000000) (35128793707 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1701193677751449 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35669665897 / 1000000000000) (-35669640775 / 1000000000000), orderedInterval (15027011297 / 1000000000000) (15027036419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1064528014581747 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5779445880 / 1000000000000) (5779445891 / 1000000000000), orderedInterval (-48577538382 / 1000000000000) (-48577538370 / 1000000000000)))) (orderedInterval (-7340630691 / 1000000000000) (-7340629344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (572506706702349 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37770889734 / 1000000000000) (-37770878627 / 1000000000000), orderedInterval (55098443542 / 1000000000000) (55098454650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1554467077114047 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6274144997 / 1000000000000) (-6274144989 / 1000000000000), orderedInterval (39993131510 / 1000000000000) (39993131517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2122491898321119 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15963505387 / 1000000000000) (-15963505386 / 1000000000000), orderedInterval (-30724605775 / 1000000000000) (-30724605774 / 1000000000000)))) (orderedInterval (1531582404 / 1000000000000) (1531582517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (897471985418253 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45987156641 / 1000000000000) (-45987123664 / 1000000000000), orderedInterval (26983137245 / 1000000000000) (26983170223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3648173794570413 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25913869200 / 1000000000000) (25913907129 / 1000000000000), orderedInterval (-5160585288 / 1000000000000) (-5160547359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2436811023574467 / 4000000000000) 1 (IntervalRat.scale (981 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16033620234 / 1000000000000) (16033620235 / 1000000000000), orderedInterval (28056894807 / 1000000000000) (28056894808 / 1000000000000)))) (orderedInterval (-5682671646 / 1000000000000) (-5682665623 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks1 :
    compactCertificate619.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate619.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate619_chunkChecks1_0
    compactCertificate619_chunkChecks1_1 compactCertificate619_chunkChecks1_2

theorem compactCertificate619_chunkChecks2_0 :
    compactCertificate619.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (981 / 2) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33534577719 / 1000000000000) (33534577721 / 1000000000000), orderedInterval (13131348260 / 1000000000000) (13131348262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1445200319890881 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30169829338 / 1000000000000) (-30169829337 / 1000000000000), orderedInterval (-29143969810 / 1000000000000) (-29143969809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (467348089938273 / 800000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19556746460 / 1000000000000) (19556746461 / 1000000000000), orderedInterval (26578199259 / 1000000000000) (26578199260 / 1000000000000)))) (orderedInterval (-14781256602 / 1000000000000) (-14781256557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (421705848963267 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44099577772 / 1000000000000) (-44099564225 / 1000000000000), orderedInterval (64191725701 / 1000000000000) (64191739248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3075667087867083 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-339739311 / 1000000000000) (-339739310 / 1000000000000), orderedInterval (-28771786656 / 1000000000000) (-28771786655 / 1000000000000)))) (orderedInterval (-632592191 / 1000000000000) (-632592091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2265522456300579 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33329826142 / 1000000000000) (33329828924 / 1000000000000), orderedInterval (-3653817813 / 1000000000000) (-3653815031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3882011343464367 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13079474669 / 1000000000000) (-13079474668 / 1000000000000), orderedInterval (-22013624384 / 1000000000000) (-22013624383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2859471985418253 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17578941763 / 1000000000000) (-17578941141 / 1000000000000), orderedInterval (24127074617 / 1000000000000) (24127075239 / 1000000000000)))) (orderedInterval (-681397398 / 1000000000000) (-681397280 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks2_1 :
    compactCertificate619.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4387165371854019 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22095487714 / 1000000000000) (-22095487585 / 1000000000000), orderedInterval (-9593455173 / 1000000000000) (-9593455044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2532931108419051 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17475342623 / 1000000000000) (-17475342037 / 1000000000000), orderedInterval (26470579374 / 1000000000000) (26470579960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4494730700584359 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5245632301 / 1000000000000) (-5245632300 / 1000000000000), orderedInterval (23219376067 / 1000000000000) (23219376068 / 1000000000000)))) (orderedInterval (-13587331135 / 1000000000000) (-13587330083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4199560461617571 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24193648742 / 1000000000000) (24193650318 / 1000000000000), orderedInterval (4574898523 / 1000000000000) (4574900100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2997004504500243 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20997203189 / 1000000000000) (20997206972 / 1000000000000), orderedInterval (-20232622543 / 1000000000000) (-20232618760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3398283684449397 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23260083930 / 1000000000000) (23260103000 / 1000000000000), orderedInterval (-14446671032 / 1000000000000) (-14446651962 / 1000000000000)))) (orderedInterval (-2272704451 / 1000000000000) (-2272703038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2833134647209893 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24051755465 / 1000000000000) (-24051738578 / 1000000000000), orderedInterval (17914840191 / 1000000000000) (17914857078 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2503160381163753 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31422182660 / 1000000000000) (-31422182534 / 1000000000000), orderedInterval (-5447712498 / 1000000000000) (-5447712372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (725513443823547 / 800000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6380531486 / 1000000000000) (6380531487 / 1000000000000), orderedInterval (-25718664340 / 1000000000000) (-25718664338 / 1000000000000)))) (orderedInterval (-2905214941 / 1000000000000) (-2905214420 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks2_2 :
    compactCertificate619.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2006808367296609 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-5941746992 / 1000000000000) (-5941746988 / 1000000000000), orderedInterval (35128793703 / 1000000000000) (35128793707 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1701193677751449 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35669665897 / 1000000000000) (-35669640775 / 1000000000000), orderedInterval (15027011297 / 1000000000000) (15027036419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1064528014581747 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5779445880 / 1000000000000) (5779445891 / 1000000000000), orderedInterval (-48577538382 / 1000000000000) (-48577538370 / 1000000000000)))) (orderedInterval (-2552188981 / 1000000000000) (-2552187800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (572506706702349 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37770889734 / 1000000000000) (-37770878627 / 1000000000000), orderedInterval (55098443542 / 1000000000000) (55098454650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1554467077114047 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6274144997 / 1000000000000) (-6274144989 / 1000000000000), orderedInterval (39993131510 / 1000000000000) (39993131517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2122491898321119 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15963505387 / 1000000000000) (-15963505386 / 1000000000000), orderedInterval (-30724605775 / 1000000000000) (-30724605774 / 1000000000000)))) (orderedInterval (-1583620798 / 1000000000000) (-1583620727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (897471985418253 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45987156641 / 1000000000000) (-45987123664 / 1000000000000), orderedInterval (26983137245 / 1000000000000) (26983170223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3648173794570413 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25913869200 / 1000000000000) (25913907129 / 1000000000000), orderedInterval (-5160585288 / 1000000000000) (-5160547359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2436811023574467 / 4000000000000) 2 (IntervalRat.scale (981 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16033620234 / 1000000000000) (16033620235 / 1000000000000), orderedInterval (28056894807 / 1000000000000) (28056894808 / 1000000000000)))) (orderedInterval (12003381740 / 1000000000000) (12003392750 / 1000000000000))) = true
  rfl'

theorem compactCertificate619_chunkChecks2 :
    compactCertificate619.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate619.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate619_chunkChecks2_0
    compactCertificate619_chunkChecks2_1 compactCertificate619_chunkChecks2_2

theorem compactCertificate619_chunkChecks3_0 :
    compactCertificate619.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (981 / 2) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33534577719 / 1000000000000) (33534577721 / 1000000000000), orderedInterval (13131348260 / 1000000000000) (13131348262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1445200319890881 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30169829338 / 1000000000000) (-30169829337 / 1000000000000), orderedInterval (-29143969810 / 1000000000000) (-29143969809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (467348089938273 / 800000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19556746460 / 1000000000000) (19556746461 / 1000000000000), orderedInterval (26578199259 / 1000000000000) (26578199260 / 1000000000000)))) (orderedInterval (-7700976191 / 1000000000000) (-7700976138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (421705848963267 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44099577772 / 1000000000000) (-44099564225 / 1000000000000), orderedInterval (64191725701 / 1000000000000) (64191739248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3075667087867083 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-339739311 / 1000000000000) (-339739310 / 1000000000000), orderedInterval (-28771786656 / 1000000000000) (-28771786655 / 1000000000000)))) (orderedInterval (-7981393589 / 1000000000000) (-7981393448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2265522456300579 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33329826142 / 1000000000000) (33329828924 / 1000000000000), orderedInterval (-3653817813 / 1000000000000) (-3653815031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3882011343464367 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13079474669 / 1000000000000) (-13079474668 / 1000000000000), orderedInterval (-22013624384 / 1000000000000) (-22013624383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2859471985418253 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17578941763 / 1000000000000) (-17578941141 / 1000000000000), orderedInterval (24127074617 / 1000000000000) (24127075239 / 1000000000000)))) (orderedInterval (-7063116465 / 1000000000000) (-7063116263 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate619_chunkChecks3_1 :
    compactCertificate619.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4387165371854019 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22095487714 / 1000000000000) (-22095487585 / 1000000000000), orderedInterval (-9593455173 / 1000000000000) (-9593455044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2532931108419051 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17475342623 / 1000000000000) (-17475342037 / 1000000000000), orderedInterval (26470579374 / 1000000000000) (26470579960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4494730700584359 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5245632301 / 1000000000000) (-5245632300 / 1000000000000), orderedInterval (23219376067 / 1000000000000) (23219376068 / 1000000000000)))) (orderedInterval (-62935930670 / 1000000000000) (-62935928426 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4199560461617571 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24193648742 / 1000000000000) (24193650318 / 1000000000000), orderedInterval (4574898523 / 1000000000000) (4574900100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2997004504500243 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20997203189 / 1000000000000) (20997206972 / 1000000000000), orderedInterval (-20232622543 / 1000000000000) (-20232618760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3398283684449397 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23260083930 / 1000000000000) (23260103000 / 1000000000000), orderedInterval (-14446671032 / 1000000000000) (-14446651962 / 1000000000000)))) (orderedInterval (7253938303 / 1000000000000) (7253940627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2833134647209893 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24051755465 / 1000000000000) (-24051738578 / 1000000000000), orderedInterval (17914840191 / 1000000000000) (17914857078 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2503160381163753 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31422182660 / 1000000000000) (-31422182534 / 1000000000000), orderedInterval (-5447712498 / 1000000000000) (-5447712372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (725513443823547 / 800000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6380531486 / 1000000000000) (6380531487 / 1000000000000), orderedInterval (-25718664340 / 1000000000000) (-25718664338 / 1000000000000)))) (orderedInterval (2897641729 / 1000000000000) (2897642488 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate619_chunkChecks3_2 :
    compactCertificate619.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2006808367296609 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-5941746992 / 1000000000000) (-5941746988 / 1000000000000), orderedInterval (35128793703 / 1000000000000) (35128793707 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1701193677751449 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35669665897 / 1000000000000) (-35669640775 / 1000000000000), orderedInterval (15027011297 / 1000000000000) (15027036419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1064528014581747 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5779445880 / 1000000000000) (5779445891 / 1000000000000), orderedInterval (-48577538382 / 1000000000000) (-48577538370 / 1000000000000)))) (orderedInterval (6822726939 / 1000000000000) (6822727974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (572506706702349 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37770889734 / 1000000000000) (-37770878627 / 1000000000000), orderedInterval (55098443542 / 1000000000000) (55098454650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1554467077114047 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6274144997 / 1000000000000) (-6274144989 / 1000000000000), orderedInterval (39993131510 / 1000000000000) (39993131517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2122491898321119 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15963505387 / 1000000000000) (-15963505386 / 1000000000000), orderedInterval (-30724605775 / 1000000000000) (-30724605774 / 1000000000000)))) (orderedInterval (-2501347516 / 1000000000000) (-2501347456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (897471985418253 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45987156641 / 1000000000000) (-45987123664 / 1000000000000), orderedInterval (26983137245 / 1000000000000) (26983170223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3648173794570413 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25913869200 / 1000000000000) (25913907129 / 1000000000000), orderedInterval (-5160585288 / 1000000000000) (-5160547359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2436811023574467 / 4000000000000) 3 (IntervalRat.scale (981 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16033620234 / 1000000000000) (16033620235 / 1000000000000), orderedInterval (28056894807 / 1000000000000) (28056894808 / 1000000000000)))) (orderedInterval (7344937363 / 1000000000000) (7344957688 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate619_chunkChecks3 :
    compactCertificate619.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate619.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate619_chunkChecks3_0
    compactCertificate619_chunkChecks3_1 compactCertificate619_chunkChecks3_2

theorem compactCertificate619_chunkChecks4_0 :
    compactCertificate619.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (981 / 2) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33534577719 / 1000000000000) (33534577721 / 1000000000000), orderedInterval (13131348260 / 1000000000000) (13131348262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1445200319890881 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30169829338 / 1000000000000) (-30169829337 / 1000000000000), orderedInterval (-29143969810 / 1000000000000) (-29143969809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (467348089938273 / 800000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19556746460 / 1000000000000) (19556746461 / 1000000000000), orderedInterval (26578199259 / 1000000000000) (26578199260 / 1000000000000)))) (orderedInterval (15549603745 / 1000000000000) (15549603806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (421705848963267 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44099577772 / 1000000000000) (-44099564225 / 1000000000000), orderedInterval (64191725701 / 1000000000000) (64191739248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3075667087867083 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-339739311 / 1000000000000) (-339739310 / 1000000000000), orderedInterval (-28771786656 / 1000000000000) (-28771786655 / 1000000000000)))) (orderedInterval (360825098 / 1000000000000) (360825313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2265522456300579 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33329826142 / 1000000000000) (33329828924 / 1000000000000), orderedInterval (-3653817813 / 1000000000000) (-3653815031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3882011343464367 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13079474669 / 1000000000000) (-13079474668 / 1000000000000), orderedInterval (-22013624384 / 1000000000000) (-22013624383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2859471985418253 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17578941763 / 1000000000000) (-17578941141 / 1000000000000), orderedInterval (24127074617 / 1000000000000) (24127075239 / 1000000000000)))) (orderedInterval (4294876469 / 1000000000000) (4294876824 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate619_chunkChecks4_1 :
    compactCertificate619.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4387165371854019 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22095487714 / 1000000000000) (-22095487585 / 1000000000000), orderedInterval (-9593455173 / 1000000000000) (-9593455044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2532931108419051 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17475342623 / 1000000000000) (-17475342037 / 1000000000000), orderedInterval (26470579374 / 1000000000000) (26470579960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4494730700584359 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5245632301 / 1000000000000) (-5245632300 / 1000000000000), orderedInterval (23219376067 / 1000000000000) (23219376068 / 1000000000000)))) (orderedInterval (74273386611 / 1000000000000) (74273391512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4199560461617571 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24193648742 / 1000000000000) (24193650318 / 1000000000000), orderedInterval (4574898523 / 1000000000000) (4574900100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2997004504500243 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20997203189 / 1000000000000) (20997206972 / 1000000000000), orderedInterval (-20232622543 / 1000000000000) (-20232618760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3398283684449397 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23260083930 / 1000000000000) (23260103000 / 1000000000000), orderedInterval (-14446671032 / 1000000000000) (-14446651962 / 1000000000000)))) (orderedInterval (553325651 / 1000000000000) (553329534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2833134647209893 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24051755465 / 1000000000000) (-24051738578 / 1000000000000), orderedInterval (17914840191 / 1000000000000) (17914857078 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2503160381163753 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31422182660 / 1000000000000) (-31422182534 / 1000000000000), orderedInterval (-5447712498 / 1000000000000) (-5447712372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (725513443823547 / 800000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6380531486 / 1000000000000) (6380531487 / 1000000000000), orderedInterval (-25718664340 / 1000000000000) (-25718664338 / 1000000000000)))) (orderedInterval (5453941849 / 1000000000000) (5453942965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate619_chunkChecks4_2 :
    compactCertificate619.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2006808367296609 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-5941746992 / 1000000000000) (-5941746988 / 1000000000000), orderedInterval (35128793703 / 1000000000000) (35128793707 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1701193677751449 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35669665897 / 1000000000000) (-35669640775 / 1000000000000), orderedInterval (15027011297 / 1000000000000) (15027036419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1064528014581747 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5779445880 / 1000000000000) (5779445891 / 1000000000000), orderedInterval (-48577538382 / 1000000000000) (-48577538370 / 1000000000000)))) (orderedInterval (2169449903 / 1000000000000) (2169450815 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (572506706702349 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37770889734 / 1000000000000) (-37770878627 / 1000000000000), orderedInterval (55098443542 / 1000000000000) (55098454650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1554467077114047 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6274144997 / 1000000000000) (-6274144989 / 1000000000000), orderedInterval (39993131510 / 1000000000000) (39993131517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2122491898321119 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15963505387 / 1000000000000) (-15963505386 / 1000000000000), orderedInterval (-30724605775 / 1000000000000) (-30724605774 / 1000000000000)))) (orderedInterval (1746916790 / 1000000000000) (1746916849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (897471985418253 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45987156641 / 1000000000000) (-45987123664 / 1000000000000), orderedInterval (26983137245 / 1000000000000) (26983170223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3648173794570413 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25913869200 / 1000000000000) (25913907129 / 1000000000000), orderedInterval (-5160585288 / 1000000000000) (-5160547359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2436811023574467 / 4000000000000) 4 (IntervalRat.scale (981 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16033620234 / 1000000000000) (16033620235 / 1000000000000), orderedInterval (28056894807 / 1000000000000) (28056894808 / 1000000000000)))) (orderedInterval (-32416263001 / 1000000000000) (-32416225306 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate619_chunkChecks4 :
    compactCertificate619.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate619.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate619_chunkChecks4_0
    compactCertificate619_chunkChecks4_1 compactCertificate619_chunkChecks4_2

theorem compactCertificate619_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate619.chunkCheck r b = true :=
  compactCertificate619.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate619_chunkChecks0
    · exact compactCertificate619_chunkChecks1
    · exact compactCertificate619_chunkChecks2
    · exact compactCertificate619_chunkChecks3
    · exact compactCertificate619_chunkChecks4)

theorem compactCertificate619_coefficient0 :
    compactCertificate619.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate619_coefficient1 :
    compactCertificate619.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate619_coefficient2 :
    compactCertificate619.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate619_coefficient3 :
    compactCertificate619.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate619_coefficient4 :
    compactCertificate619.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate619_coefficients : ∀ r : Fin 5,
    compactCertificate619.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate619_coefficient0
  · exact compactCertificate619_coefficient1
  · exact compactCertificate619_coefficient2
  · exact compactCertificate619_coefficient3
  · exact compactCertificate619_coefficient4

theorem compactCertificate619_lower : (1 : ℚ) ≤ compactCertificate619.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate619, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate619_proves {t : ℝ} (ht : t ∈ compactCertificate619.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate619.proves compactCertificate619_states compactCertificate619_chunks
    compactCertificate619_coefficients compactCertificate619_lower ht

end Erdos232
