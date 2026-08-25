/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate403 : CompactCertificate where
  left := 274
  right := 275
  center := 549 / 2
  grid := fun i =>
    match i.val with
    | 0 => 87
    | 1 => 64
    | 2 => 104
    | 3 => 19
    | 4 => 50
    | 5 => 137
    | 6 => 101
    | 7 => 173
    | 8 => 127
    | 9 => 195
    | 10 => 113
    | 11 => 200
    | 12 => 187
    | 13 => 134
    | 14 => 151
    | 15 => 126
    | 16 => 112
    | 17 => 162
    | 18 => 89
    | 19 => 76
    | 20 => 47
    | 21 => 26
    | 22 => 69
    | 23 => 95
    | 24 => 40
    | 25 => 163
    | _ => 109
  point := fun i =>
    match i.val with
    | 0 => 549 / 2
    | 1 => 808781830397649 / 4000000000000
    | 2 => 261543426479217 / 800000000000
    | 3 => 236000520979443 / 4000000000000
    | 4 => 633930595570071 / 4000000000000
    | 5 => 1721244884035707 / 4000000000000
    | 6 => 1267861191140691 / 4000000000000
    | 7 => 2172501761021343 / 4000000000000
    | 8 => 1600254964316637 / 4000000000000
    | 9 => 2455202639294451 / 4000000000000
    | 10 => 1417511904711579 / 4000000000000
    | 11 => 2515399749868311 / 4000000000000
    | 12 => 2350212735400659 / 4000000000000
    | 13 => 1677222704353347 / 4000000000000
    | 14 => 1901791786710213 / 4000000000000
    | 15 => 1585515719998197 / 4000000000000
    | 16 => 1400851222486137 / 4000000000000
    | 17 => 406021285075563 / 800000000000
    | 18 => 1123076242248561 / 4000000000000
    | 19 => 952044168282921 / 4000000000000
    | 20 => 595745035683363 / 4000000000000
    | 21 => 320393661549021 / 4000000000000
    | 22 => 869931116550063 / 4000000000000
    | 23 => 1187816566950351 / 4000000000000
    | 24 => 502254964316637 / 4000000000000
    | 25 => 2041638545585277 / 4000000000000
    | _ => 1363719930624243 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-44438823121 / 1000000000000) (-44438811256 / 1000000000000), orderedInterval (18638592502 / 1000000000000) (18638604366 / 1000000000000))
    | 1 => (orderedInterval (52757549309 / 1000000000000) (52757554327 / 1000000000000), orderedInterval (-19239879711 / 1000000000000) (-19239874693 / 1000000000000))
    | 2 => (orderedInterval (36859633453 / 1000000000000) (36859633454 / 1000000000000), orderedInterval (24205472051 / 1000000000000) (24205472052 / 1000000000000))
    | 3 => (orderedInterval (-9661818101 / 1000000000000) (-9661818099 / 1000000000000), orderedInterval (-103345258435 / 1000000000000) (-103345258432 / 1000000000000))
    | 4 => (orderedInterval (51699602181 / 1000000000000) (51699655916 / 1000000000000), orderedInterval (-36825236557 / 1000000000000) (-36825182822 / 1000000000000))
    | 5 => (orderedInterval (-24723950087 / 1000000000000) (-24723950086 / 1000000000000), orderedInterval (-29435942250 / 1000000000000) (-29435942249 / 1000000000000))
    | 6 => (orderedInterval (-19470995785 / 1000000000000) (-19470995784 / 1000000000000), orderedInterval (-40334691532 / 1000000000000) (-40334691531 / 1000000000000))
    | 7 => (orderedInterval (-13806310381 / 1000000000000) (-13806310380 / 1000000000000), orderedInterval (-31316628478 / 1000000000000) (-31316628477 / 1000000000000))
    | 8 => (orderedInterval (-38158965328 / 1000000000000) (-38158957067 / 1000000000000), orderedInterval (11674745434 / 1000000000000) (11674753695 / 1000000000000))
    | 9 => (orderedInterval (-29606389141 / 1000000000000) (-29606326274 / 1000000000000), orderedInterval (12698470594 / 1000000000000) (12698533462 / 1000000000000))
    | 10 => (orderedInterval (-6880276740 / 1000000000000) (-6880276739 / 1000000000000), orderedInterval (-41812610804 / 1000000000000) (-41812610803 / 1000000000000))
    | 11 => (orderedInterval (30795146607 / 1000000000000) (30795146647 / 1000000000000), orderedInterval (7976407848 / 1000000000000) (7976407888 / 1000000000000))
    | 12 => (orderedInterval (-24957340946 / 1000000000000) (-24957340945 / 1000000000000), orderedInterval (-21441313031 / 1000000000000) (-21441313030 / 1000000000000))
    | 13 => (orderedInterval (-30097274242 / 1000000000000) (-30097232425 / 1000000000000), orderedInterval (24783118133 / 1000000000000) (24783159951 / 1000000000000))
    | 14 => (orderedInterval (-35148924824 / 1000000000000) (-35148914293 / 1000000000000), orderedInterval (10212529398 / 1000000000000) (10212539929 / 1000000000000))
    | 15 => (orderedInterval (38855235333 / 1000000000000) (38855235341 / 1000000000000), orderedInterval (9767218463 / 1000000000000) (9767218470 / 1000000000000))
    | 16 => (orderedInterval (-32325950887 / 1000000000000) (-32325903995 / 1000000000000), orderedInterval (27846172059 / 1000000000000) (27846218951 / 1000000000000))
    | 17 => (orderedInterval (-20758266625 / 1000000000000) (-20758264571 / 1000000000000), orderedInterval (28716303309 / 1000000000000) (28716305363 / 1000000000000))
    | 18 => (orderedInterval (-44194511459 / 1000000000000) (-44194500811 / 1000000000000), orderedInterval (17805999939 / 1000000000000) (17806010587 / 1000000000000))
    | 19 => (orderedInterval (1803213063 / 1000000000000) (1803213065 / 1000000000000), orderedInterval (51682798270 / 1000000000000) (51682798272 / 1000000000000))
    | 20 => (orderedInterval (-57526347623 / 1000000000000) (-57526330749 / 1000000000000), orderedInterval (31260001261 / 1000000000000) (31260018135 / 1000000000000))
    | 21 => (orderedInterval (-63900256994 / 1000000000000) (-63900167801 / 1000000000000), orderedInterval (62565758239 / 1000000000000) (62565847432 / 1000000000000))
    | 22 => (orderedInterval (-53959272166 / 1000000000000) (-53959272139 / 1000000000000), orderedInterval (-3826708656 / 1000000000000) (-3826708630 / 1000000000000))
    | 23 => (orderedInterval (30257458205 / 1000000000000) (30257473472 / 1000000000000), orderedInterval (-35098323347 / 1000000000000) (-35098308080 / 1000000000000))
    | 24 => (orderedInterval (45018020659 / 1000000000000) (45018020660 / 1000000000000), orderedInterval (54988468024 / 1000000000000) (54988468025 / 1000000000000))
    | 25 => (orderedInterval (27327949023 / 1000000000000) (27327977082 / 1000000000000), orderedInterval (-22397625623 / 1000000000000) (-22397597564 / 1000000000000))
    | _ => (orderedInterval (28447515588 / 1000000000000) (28447528678 / 1000000000000), orderedInterval (-32569289012 / 1000000000000) (-32569275922 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14959430504 / 1000000000000) (-14959425735 / 1000000000000)
      | 1 => orderedInterval (3750083338 / 1000000000000) (3750085334 / 1000000000000)
      | 2 => orderedInterval (-496385061 / 1000000000000) (-496384845 / 1000000000000)
      | 3 => orderedInterval (9128626304 / 1000000000000) (9128637590 / 1000000000000)
      | 4 => orderedInterval (-2217653753 / 1000000000000) (-2217649712 / 1000000000000)
      | 5 => orderedInterval (1767097868 / 1000000000000) (1767100631 / 1000000000000)
      | 6 => orderedInterval (5091519006 / 1000000000000) (5091521328 / 1000000000000)
      | 7 => orderedInterval (85192043 / 1000000000000) (85194894 / 1000000000000)
      | _ => orderedInterval (-7290673548 / 1000000000000) (-7290668731 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (8947330820 / 1000000000000) (8947335579 / 1000000000000)
      | 1 => orderedInterval (2745096749 / 1000000000000) (2745097920 / 1000000000000)
      | 2 => orderedInterval (2322409574 / 1000000000000) (2322409892 / 1000000000000)
      | 3 => orderedInterval (-6447245365 / 1000000000000) (-6447220148 / 1000000000000)
      | 4 => orderedInterval (4318865304 / 1000000000000) (4318871490 / 1000000000000)
      | 5 => orderedInterval (-510798004 / 1000000000000) (-510794444 / 1000000000000)
      | 6 => orderedInterval (-4896298202 / 1000000000000) (-4896296098 / 1000000000000)
      | 7 => orderedInterval (2641602160 / 1000000000000) (2641603937 / 1000000000000)
      | _ => orderedInterval (11131436707 / 1000000000000) (11131444111 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14246545165 / 1000000000000) (14246549935 / 1000000000000)
      | 1 => orderedInterval (-4963272928 / 1000000000000) (-4963272217 / 1000000000000)
      | 2 => orderedInterval (283326702 / 1000000000000) (283327176 / 1000000000000)
      | 3 => orderedInterval (-48405433902 / 1000000000000) (-48405377443 / 1000000000000)
      | 4 => orderedInterval (4027263172 / 1000000000000) (4027272669 / 1000000000000)
      | 5 => orderedInterval (-2127946029 / 1000000000000) (-2127941411 / 1000000000000)
      | 6 => orderedInterval (-6746930023 / 1000000000000) (-6746928012 / 1000000000000)
      | 7 => orderedInterval (1835264824 / 1000000000000) (1835266370 / 1000000000000)
      | _ => orderedInterval (15827357462 / 1000000000000) (15827369332 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9767464133 / 1000000000000) (-9767459365 / 1000000000000)
      | 1 => orderedInterval (-7795559389 / 1000000000000) (-7795558930 / 1000000000000)
      | 2 => orderedInterval (-8356498365 / 1000000000000) (-8356497658 / 1000000000000)
      | 3 => orderedInterval (18436114657 / 1000000000000) (18436240882 / 1000000000000)
      | 4 => orderedInterval (-11894992770 / 1000000000000) (-11894978215 / 1000000000000)
      | 5 => orderedInterval (-1669711193 / 1000000000000) (-1669705184 / 1000000000000)
      | 6 => orderedInterval (4815454985 / 1000000000000) (4815456961 / 1000000000000)
      | 7 => orderedInterval (-3426590124 / 1000000000000) (-3426588565 / 1000000000000)
      | _ => orderedInterval (-23517944765 / 1000000000000) (-23517925090 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13045854736 / 1000000000000) (-13045849951 / 1000000000000)
      | 1 => orderedInterval (10880850037 / 1000000000000) (10880850378 / 1000000000000)
      | 2 => orderedInterval (2426496874 / 1000000000000) (2426497941 / 1000000000000)
      | 3 => orderedInterval (250543543026 / 1000000000000) (250543825710 / 1000000000000)
      | 4 => orderedInterval (-4350423415 / 1000000000000) (-4350401042 / 1000000000000)
      | 5 => orderedInterval (653182777 / 1000000000000) (653190683 / 1000000000000)
      | 6 => orderedInterval (7479186140 / 1000000000000) (7479188124 / 1000000000000)
      | 7 => orderedInterval (-2660018855 / 1000000000000) (-2660017197 / 1000000000000)
      | _ => orderedInterval (-39109113420 / 1000000000000) (-39109079741 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-5141624307 / 1000000000000) (-5141589246 / 1000000000000)
    | 1 => orderedInterval (20252399743 / 1000000000000) (20252452239 / 1000000000000)
    | 2 => orderedInterval (-26023825557 / 1000000000000) (-26023733601 / 1000000000000)
    | 3 => orderedInterval (-43177191097 / 1000000000000) (-43177015164 / 1000000000000)
    | _ => orderedInterval (212817848428 / 1000000000000) (212818204905 / 1000000000000)

theorem compactCertificate403_stateChecks0 :
    compactCertificate403.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (549 / 2)) (orderedInterval (-44438823121 / 1000000000000) (-44438811256 / 1000000000000), orderedInterval (18638592502 / 1000000000000) (18638604366 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (808781830397649 / 4000000000000)) (orderedInterval (52757549309 / 1000000000000) (52757554327 / 1000000000000), orderedInterval (-19239879711 / 1000000000000) (-19239874693 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (261543426479217 / 800000000000)) (orderedInterval (36859633453 / 1000000000000) (36859633454 / 1000000000000), orderedInterval (24205472051 / 1000000000000) (24205472052 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_stateChecks1 :
    compactCertificate403.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (236000520979443 / 4000000000000)) (orderedInterval (-9661818101 / 1000000000000) (-9661818099 / 1000000000000), orderedInterval (-103345258435 / 1000000000000) (-103345258432 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (633930595570071 / 4000000000000)) (orderedInterval (51699602181 / 1000000000000) (51699655916 / 1000000000000), orderedInterval (-36825236557 / 1000000000000) (-36825182822 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1721244884035707 / 4000000000000)) (orderedInterval (-24723950087 / 1000000000000) (-24723950086 / 1000000000000), orderedInterval (-29435942250 / 1000000000000) (-29435942249 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_stateChecks2 :
    compactCertificate403.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1267861191140691 / 4000000000000)) (orderedInterval (-19470995785 / 1000000000000) (-19470995784 / 1000000000000), orderedInterval (-40334691532 / 1000000000000) (-40334691531 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2172501761021343 / 4000000000000)) (orderedInterval (-13806310381 / 1000000000000) (-13806310380 / 1000000000000), orderedInterval (-31316628478 / 1000000000000) (-31316628477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1600254964316637 / 4000000000000)) (orderedInterval (-38158965328 / 1000000000000) (-38158957067 / 1000000000000), orderedInterval (11674745434 / 1000000000000) (11674753695 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_stateChecks3 :
    compactCertificate403.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2455202639294451 / 4000000000000)) (orderedInterval (-29606389141 / 1000000000000) (-29606326274 / 1000000000000), orderedInterval (12698470594 / 1000000000000) (12698533462 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1417511904711579 / 4000000000000)) (orderedInterval (-6880276740 / 1000000000000) (-6880276739 / 1000000000000), orderedInterval (-41812610804 / 1000000000000) (-41812610803 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2515399749868311 / 4000000000000)) (orderedInterval (30795146607 / 1000000000000) (30795146647 / 1000000000000), orderedInterval (7976407848 / 1000000000000) (7976407888 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_stateChecks4 :
    compactCertificate403.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2350212735400659 / 4000000000000)) (orderedInterval (-24957340946 / 1000000000000) (-24957340945 / 1000000000000), orderedInterval (-21441313031 / 1000000000000) (-21441313030 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1677222704353347 / 4000000000000)) (orderedInterval (-30097274242 / 1000000000000) (-30097232425 / 1000000000000), orderedInterval (24783118133 / 1000000000000) (24783159951 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1901791786710213 / 4000000000000)) (orderedInterval (-35148924824 / 1000000000000) (-35148914293 / 1000000000000), orderedInterval (10212529398 / 1000000000000) (10212539929 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_stateChecks5 :
    compactCertificate403.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1585515719998197 / 4000000000000)) (orderedInterval (38855235333 / 1000000000000) (38855235341 / 1000000000000), orderedInterval (9767218463 / 1000000000000) (9767218470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1400851222486137 / 4000000000000)) (orderedInterval (-32325950887 / 1000000000000) (-32325903995 / 1000000000000), orderedInterval (27846172059 / 1000000000000) (27846218951 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (406021285075563 / 800000000000)) (orderedInterval (-20758266625 / 1000000000000) (-20758264571 / 1000000000000), orderedInterval (28716303309 / 1000000000000) (28716305363 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_stateChecks6 :
    compactCertificate403.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1123076242248561 / 4000000000000)) (orderedInterval (-44194511459 / 1000000000000) (-44194500811 / 1000000000000), orderedInterval (17805999939 / 1000000000000) (17806010587 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (952044168282921 / 4000000000000)) (orderedInterval (1803213063 / 1000000000000) (1803213065 / 1000000000000), orderedInterval (51682798270 / 1000000000000) (51682798272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (595745035683363 / 4000000000000)) (orderedInterval (-57526347623 / 1000000000000) (-57526330749 / 1000000000000), orderedInterval (31260001261 / 1000000000000) (31260018135 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_stateChecks7 :
    compactCertificate403.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (320393661549021 / 4000000000000)) (orderedInterval (-63900256994 / 1000000000000) (-63900167801 / 1000000000000), orderedInterval (62565758239 / 1000000000000) (62565847432 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (869931116550063 / 4000000000000)) (orderedInterval (-53959272166 / 1000000000000) (-53959272139 / 1000000000000), orderedInterval (-3826708656 / 1000000000000) (-3826708630 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1187816566950351 / 4000000000000)) (orderedInterval (30257458205 / 1000000000000) (30257473472 / 1000000000000), orderedInterval (-35098323347 / 1000000000000) (-35098308080 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_stateChecks8 :
    compactCertificate403.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (502254964316637 / 4000000000000)) (orderedInterval (45018020659 / 1000000000000) (45018020660 / 1000000000000), orderedInterval (54988468024 / 1000000000000) (54988468025 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2041638545585277 / 4000000000000)) (orderedInterval (27327949023 / 1000000000000) (27327977082 / 1000000000000), orderedInterval (-22397625623 / 1000000000000) (-22397597564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1363719930624243 / 4000000000000)) (orderedInterval (28447515588 / 1000000000000) (28447528678 / 1000000000000), orderedInterval (-32569289012 / 1000000000000) (-32569275922 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_states : ∀ j,
    BesselStateValid (compactCertificate403.point j) (compactCertificate403.state j) :=
  compactCertificate403.statesValid_of_checks3 compactCertificate403_stateChecks0
    compactCertificate403_stateChecks1 compactCertificate403_stateChecks2
    compactCertificate403_stateChecks3 compactCertificate403_stateChecks4
    compactCertificate403_stateChecks5 compactCertificate403_stateChecks6
    compactCertificate403_stateChecks7 compactCertificate403_stateChecks8

theorem compactCertificate403_chunkChecks0_0 :
    compactCertificate403.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (549 / 2) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44438823121 / 1000000000000) (-44438811256 / 1000000000000), orderedInterval (18638592502 / 1000000000000) (18638604366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (808781830397649 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52757549309 / 1000000000000) (52757554327 / 1000000000000), orderedInterval (-19239879711 / 1000000000000) (-19239874693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (261543426479217 / 800000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36859633453 / 1000000000000) (36859633454 / 1000000000000), orderedInterval (24205472051 / 1000000000000) (24205472052 / 1000000000000)))) (orderedInterval (-14959430504 / 1000000000000) (-14959425735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (236000520979443 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9661818101 / 1000000000000) (-9661818099 / 1000000000000), orderedInterval (-103345258435 / 1000000000000) (-103345258432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (633930595570071 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51699602181 / 1000000000000) (51699655916 / 1000000000000), orderedInterval (-36825236557 / 1000000000000) (-36825182822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1721244884035707 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24723950087 / 1000000000000) (-24723950086 / 1000000000000), orderedInterval (-29435942250 / 1000000000000) (-29435942249 / 1000000000000)))) (orderedInterval (3750083338 / 1000000000000) (3750085334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1267861191140691 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19470995785 / 1000000000000) (-19470995784 / 1000000000000), orderedInterval (-40334691532 / 1000000000000) (-40334691531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2172501761021343 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13806310381 / 1000000000000) (-13806310380 / 1000000000000), orderedInterval (-31316628478 / 1000000000000) (-31316628477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1600254964316637 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38158965328 / 1000000000000) (-38158957067 / 1000000000000), orderedInterval (11674745434 / 1000000000000) (11674753695 / 1000000000000)))) (orderedInterval (-496385061 / 1000000000000) (-496384845 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks0_1 :
    compactCertificate403.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2455202639294451 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29606389141 / 1000000000000) (-29606326274 / 1000000000000), orderedInterval (12698470594 / 1000000000000) (12698533462 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1417511904711579 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6880276740 / 1000000000000) (-6880276739 / 1000000000000), orderedInterval (-41812610804 / 1000000000000) (-41812610803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2515399749868311 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30795146607 / 1000000000000) (30795146647 / 1000000000000), orderedInterval (7976407848 / 1000000000000) (7976407888 / 1000000000000)))) (orderedInterval (9128626304 / 1000000000000) (9128637590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2350212735400659 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24957340946 / 1000000000000) (-24957340945 / 1000000000000), orderedInterval (-21441313031 / 1000000000000) (-21441313030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1677222704353347 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30097274242 / 1000000000000) (-30097232425 / 1000000000000), orderedInterval (24783118133 / 1000000000000) (24783159951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1901791786710213 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35148924824 / 1000000000000) (-35148914293 / 1000000000000), orderedInterval (10212529398 / 1000000000000) (10212539929 / 1000000000000)))) (orderedInterval (-2217653753 / 1000000000000) (-2217649712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1585515719998197 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38855235333 / 1000000000000) (38855235341 / 1000000000000), orderedInterval (9767218463 / 1000000000000) (9767218470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1400851222486137 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32325950887 / 1000000000000) (-32325903995 / 1000000000000), orderedInterval (27846172059 / 1000000000000) (27846218951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (406021285075563 / 800000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20758266625 / 1000000000000) (-20758264571 / 1000000000000), orderedInterval (28716303309 / 1000000000000) (28716305363 / 1000000000000)))) (orderedInterval (1767097868 / 1000000000000) (1767100631 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks0_2 :
    compactCertificate403.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1123076242248561 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44194511459 / 1000000000000) (-44194500811 / 1000000000000), orderedInterval (17805999939 / 1000000000000) (17806010587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (952044168282921 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1803213063 / 1000000000000) (1803213065 / 1000000000000), orderedInterval (51682798270 / 1000000000000) (51682798272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (595745035683363 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57526347623 / 1000000000000) (-57526330749 / 1000000000000), orderedInterval (31260001261 / 1000000000000) (31260018135 / 1000000000000)))) (orderedInterval (5091519006 / 1000000000000) (5091521328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (320393661549021 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63900256994 / 1000000000000) (-63900167801 / 1000000000000), orderedInterval (62565758239 / 1000000000000) (62565847432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (869931116550063 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53959272166 / 1000000000000) (-53959272139 / 1000000000000), orderedInterval (-3826708656 / 1000000000000) (-3826708630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1187816566950351 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30257458205 / 1000000000000) (30257473472 / 1000000000000), orderedInterval (-35098323347 / 1000000000000) (-35098308080 / 1000000000000)))) (orderedInterval (85192043 / 1000000000000) (85194894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (502254964316637 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45018020659 / 1000000000000) (45018020660 / 1000000000000), orderedInterval (54988468024 / 1000000000000) (54988468025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2041638545585277 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27327949023 / 1000000000000) (27327977082 / 1000000000000), orderedInterval (-22397625623 / 1000000000000) (-22397597564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1363719930624243 / 4000000000000) 0 (IntervalRat.scale (549 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28447515588 / 1000000000000) (28447528678 / 1000000000000), orderedInterval (-32569289012 / 1000000000000) (-32569275922 / 1000000000000)))) (orderedInterval (-7290673548 / 1000000000000) (-7290668731 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks0 :
    compactCertificate403.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate403.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate403_chunkChecks0_0
    compactCertificate403_chunkChecks0_1 compactCertificate403_chunkChecks0_2

theorem compactCertificate403_chunkChecks1_0 :
    compactCertificate403.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (549 / 2) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44438823121 / 1000000000000) (-44438811256 / 1000000000000), orderedInterval (18638592502 / 1000000000000) (18638604366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (808781830397649 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52757549309 / 1000000000000) (52757554327 / 1000000000000), orderedInterval (-19239879711 / 1000000000000) (-19239874693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (261543426479217 / 800000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36859633453 / 1000000000000) (36859633454 / 1000000000000), orderedInterval (24205472051 / 1000000000000) (24205472052 / 1000000000000)))) (orderedInterval (8947330820 / 1000000000000) (8947335579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (236000520979443 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9661818101 / 1000000000000) (-9661818099 / 1000000000000), orderedInterval (-103345258435 / 1000000000000) (-103345258432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (633930595570071 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51699602181 / 1000000000000) (51699655916 / 1000000000000), orderedInterval (-36825236557 / 1000000000000) (-36825182822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1721244884035707 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24723950087 / 1000000000000) (-24723950086 / 1000000000000), orderedInterval (-29435942250 / 1000000000000) (-29435942249 / 1000000000000)))) (orderedInterval (2745096749 / 1000000000000) (2745097920 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1267861191140691 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19470995785 / 1000000000000) (-19470995784 / 1000000000000), orderedInterval (-40334691532 / 1000000000000) (-40334691531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2172501761021343 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13806310381 / 1000000000000) (-13806310380 / 1000000000000), orderedInterval (-31316628478 / 1000000000000) (-31316628477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1600254964316637 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38158965328 / 1000000000000) (-38158957067 / 1000000000000), orderedInterval (11674745434 / 1000000000000) (11674753695 / 1000000000000)))) (orderedInterval (2322409574 / 1000000000000) (2322409892 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks1_1 :
    compactCertificate403.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2455202639294451 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29606389141 / 1000000000000) (-29606326274 / 1000000000000), orderedInterval (12698470594 / 1000000000000) (12698533462 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1417511904711579 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6880276740 / 1000000000000) (-6880276739 / 1000000000000), orderedInterval (-41812610804 / 1000000000000) (-41812610803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2515399749868311 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30795146607 / 1000000000000) (30795146647 / 1000000000000), orderedInterval (7976407848 / 1000000000000) (7976407888 / 1000000000000)))) (orderedInterval (-6447245365 / 1000000000000) (-6447220148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2350212735400659 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24957340946 / 1000000000000) (-24957340945 / 1000000000000), orderedInterval (-21441313031 / 1000000000000) (-21441313030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1677222704353347 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30097274242 / 1000000000000) (-30097232425 / 1000000000000), orderedInterval (24783118133 / 1000000000000) (24783159951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1901791786710213 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35148924824 / 1000000000000) (-35148914293 / 1000000000000), orderedInterval (10212529398 / 1000000000000) (10212539929 / 1000000000000)))) (orderedInterval (4318865304 / 1000000000000) (4318871490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1585515719998197 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38855235333 / 1000000000000) (38855235341 / 1000000000000), orderedInterval (9767218463 / 1000000000000) (9767218470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1400851222486137 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32325950887 / 1000000000000) (-32325903995 / 1000000000000), orderedInterval (27846172059 / 1000000000000) (27846218951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (406021285075563 / 800000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20758266625 / 1000000000000) (-20758264571 / 1000000000000), orderedInterval (28716303309 / 1000000000000) (28716305363 / 1000000000000)))) (orderedInterval (-510798004 / 1000000000000) (-510794444 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks1_2 :
    compactCertificate403.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1123076242248561 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44194511459 / 1000000000000) (-44194500811 / 1000000000000), orderedInterval (17805999939 / 1000000000000) (17806010587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (952044168282921 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1803213063 / 1000000000000) (1803213065 / 1000000000000), orderedInterval (51682798270 / 1000000000000) (51682798272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (595745035683363 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57526347623 / 1000000000000) (-57526330749 / 1000000000000), orderedInterval (31260001261 / 1000000000000) (31260018135 / 1000000000000)))) (orderedInterval (-4896298202 / 1000000000000) (-4896296098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (320393661549021 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63900256994 / 1000000000000) (-63900167801 / 1000000000000), orderedInterval (62565758239 / 1000000000000) (62565847432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (869931116550063 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53959272166 / 1000000000000) (-53959272139 / 1000000000000), orderedInterval (-3826708656 / 1000000000000) (-3826708630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1187816566950351 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30257458205 / 1000000000000) (30257473472 / 1000000000000), orderedInterval (-35098323347 / 1000000000000) (-35098308080 / 1000000000000)))) (orderedInterval (2641602160 / 1000000000000) (2641603937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (502254964316637 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45018020659 / 1000000000000) (45018020660 / 1000000000000), orderedInterval (54988468024 / 1000000000000) (54988468025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2041638545585277 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27327949023 / 1000000000000) (27327977082 / 1000000000000), orderedInterval (-22397625623 / 1000000000000) (-22397597564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1363719930624243 / 4000000000000) 1 (IntervalRat.scale (549 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28447515588 / 1000000000000) (28447528678 / 1000000000000), orderedInterval (-32569289012 / 1000000000000) (-32569275922 / 1000000000000)))) (orderedInterval (11131436707 / 1000000000000) (11131444111 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks1 :
    compactCertificate403.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate403.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate403_chunkChecks1_0
    compactCertificate403_chunkChecks1_1 compactCertificate403_chunkChecks1_2

theorem compactCertificate403_chunkChecks2_0 :
    compactCertificate403.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (549 / 2) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44438823121 / 1000000000000) (-44438811256 / 1000000000000), orderedInterval (18638592502 / 1000000000000) (18638604366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (808781830397649 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52757549309 / 1000000000000) (52757554327 / 1000000000000), orderedInterval (-19239879711 / 1000000000000) (-19239874693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (261543426479217 / 800000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36859633453 / 1000000000000) (36859633454 / 1000000000000), orderedInterval (24205472051 / 1000000000000) (24205472052 / 1000000000000)))) (orderedInterval (14246545165 / 1000000000000) (14246549935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (236000520979443 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9661818101 / 1000000000000) (-9661818099 / 1000000000000), orderedInterval (-103345258435 / 1000000000000) (-103345258432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (633930595570071 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51699602181 / 1000000000000) (51699655916 / 1000000000000), orderedInterval (-36825236557 / 1000000000000) (-36825182822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1721244884035707 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24723950087 / 1000000000000) (-24723950086 / 1000000000000), orderedInterval (-29435942250 / 1000000000000) (-29435942249 / 1000000000000)))) (orderedInterval (-4963272928 / 1000000000000) (-4963272217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1267861191140691 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19470995785 / 1000000000000) (-19470995784 / 1000000000000), orderedInterval (-40334691532 / 1000000000000) (-40334691531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2172501761021343 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13806310381 / 1000000000000) (-13806310380 / 1000000000000), orderedInterval (-31316628478 / 1000000000000) (-31316628477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1600254964316637 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38158965328 / 1000000000000) (-38158957067 / 1000000000000), orderedInterval (11674745434 / 1000000000000) (11674753695 / 1000000000000)))) (orderedInterval (283326702 / 1000000000000) (283327176 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks2_1 :
    compactCertificate403.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2455202639294451 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29606389141 / 1000000000000) (-29606326274 / 1000000000000), orderedInterval (12698470594 / 1000000000000) (12698533462 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1417511904711579 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6880276740 / 1000000000000) (-6880276739 / 1000000000000), orderedInterval (-41812610804 / 1000000000000) (-41812610803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2515399749868311 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30795146607 / 1000000000000) (30795146647 / 1000000000000), orderedInterval (7976407848 / 1000000000000) (7976407888 / 1000000000000)))) (orderedInterval (-48405433902 / 1000000000000) (-48405377443 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2350212735400659 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24957340946 / 1000000000000) (-24957340945 / 1000000000000), orderedInterval (-21441313031 / 1000000000000) (-21441313030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1677222704353347 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30097274242 / 1000000000000) (-30097232425 / 1000000000000), orderedInterval (24783118133 / 1000000000000) (24783159951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1901791786710213 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35148924824 / 1000000000000) (-35148914293 / 1000000000000), orderedInterval (10212529398 / 1000000000000) (10212539929 / 1000000000000)))) (orderedInterval (4027263172 / 1000000000000) (4027272669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1585515719998197 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38855235333 / 1000000000000) (38855235341 / 1000000000000), orderedInterval (9767218463 / 1000000000000) (9767218470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1400851222486137 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32325950887 / 1000000000000) (-32325903995 / 1000000000000), orderedInterval (27846172059 / 1000000000000) (27846218951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (406021285075563 / 800000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20758266625 / 1000000000000) (-20758264571 / 1000000000000), orderedInterval (28716303309 / 1000000000000) (28716305363 / 1000000000000)))) (orderedInterval (-2127946029 / 1000000000000) (-2127941411 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks2_2 :
    compactCertificate403.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1123076242248561 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44194511459 / 1000000000000) (-44194500811 / 1000000000000), orderedInterval (17805999939 / 1000000000000) (17806010587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (952044168282921 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1803213063 / 1000000000000) (1803213065 / 1000000000000), orderedInterval (51682798270 / 1000000000000) (51682798272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (595745035683363 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57526347623 / 1000000000000) (-57526330749 / 1000000000000), orderedInterval (31260001261 / 1000000000000) (31260018135 / 1000000000000)))) (orderedInterval (-6746930023 / 1000000000000) (-6746928012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (320393661549021 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63900256994 / 1000000000000) (-63900167801 / 1000000000000), orderedInterval (62565758239 / 1000000000000) (62565847432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (869931116550063 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53959272166 / 1000000000000) (-53959272139 / 1000000000000), orderedInterval (-3826708656 / 1000000000000) (-3826708630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1187816566950351 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30257458205 / 1000000000000) (30257473472 / 1000000000000), orderedInterval (-35098323347 / 1000000000000) (-35098308080 / 1000000000000)))) (orderedInterval (1835264824 / 1000000000000) (1835266370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (502254964316637 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45018020659 / 1000000000000) (45018020660 / 1000000000000), orderedInterval (54988468024 / 1000000000000) (54988468025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2041638545585277 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27327949023 / 1000000000000) (27327977082 / 1000000000000), orderedInterval (-22397625623 / 1000000000000) (-22397597564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1363719930624243 / 4000000000000) 2 (IntervalRat.scale (549 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28447515588 / 1000000000000) (28447528678 / 1000000000000), orderedInterval (-32569289012 / 1000000000000) (-32569275922 / 1000000000000)))) (orderedInterval (15827357462 / 1000000000000) (15827369332 / 1000000000000))) = true
  rfl'

theorem compactCertificate403_chunkChecks2 :
    compactCertificate403.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate403.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate403_chunkChecks2_0
    compactCertificate403_chunkChecks2_1 compactCertificate403_chunkChecks2_2

theorem compactCertificate403_chunkChecks3_0 :
    compactCertificate403.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (549 / 2) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44438823121 / 1000000000000) (-44438811256 / 1000000000000), orderedInterval (18638592502 / 1000000000000) (18638604366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (808781830397649 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52757549309 / 1000000000000) (52757554327 / 1000000000000), orderedInterval (-19239879711 / 1000000000000) (-19239874693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (261543426479217 / 800000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36859633453 / 1000000000000) (36859633454 / 1000000000000), orderedInterval (24205472051 / 1000000000000) (24205472052 / 1000000000000)))) (orderedInterval (-9767464133 / 1000000000000) (-9767459365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (236000520979443 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9661818101 / 1000000000000) (-9661818099 / 1000000000000), orderedInterval (-103345258435 / 1000000000000) (-103345258432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (633930595570071 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51699602181 / 1000000000000) (51699655916 / 1000000000000), orderedInterval (-36825236557 / 1000000000000) (-36825182822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1721244884035707 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24723950087 / 1000000000000) (-24723950086 / 1000000000000), orderedInterval (-29435942250 / 1000000000000) (-29435942249 / 1000000000000)))) (orderedInterval (-7795559389 / 1000000000000) (-7795558930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1267861191140691 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19470995785 / 1000000000000) (-19470995784 / 1000000000000), orderedInterval (-40334691532 / 1000000000000) (-40334691531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2172501761021343 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13806310381 / 1000000000000) (-13806310380 / 1000000000000), orderedInterval (-31316628478 / 1000000000000) (-31316628477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1600254964316637 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38158965328 / 1000000000000) (-38158957067 / 1000000000000), orderedInterval (11674745434 / 1000000000000) (11674753695 / 1000000000000)))) (orderedInterval (-8356498365 / 1000000000000) (-8356497658 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate403_chunkChecks3_1 :
    compactCertificate403.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2455202639294451 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29606389141 / 1000000000000) (-29606326274 / 1000000000000), orderedInterval (12698470594 / 1000000000000) (12698533462 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1417511904711579 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6880276740 / 1000000000000) (-6880276739 / 1000000000000), orderedInterval (-41812610804 / 1000000000000) (-41812610803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2515399749868311 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30795146607 / 1000000000000) (30795146647 / 1000000000000), orderedInterval (7976407848 / 1000000000000) (7976407888 / 1000000000000)))) (orderedInterval (18436114657 / 1000000000000) (18436240882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2350212735400659 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24957340946 / 1000000000000) (-24957340945 / 1000000000000), orderedInterval (-21441313031 / 1000000000000) (-21441313030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1677222704353347 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30097274242 / 1000000000000) (-30097232425 / 1000000000000), orderedInterval (24783118133 / 1000000000000) (24783159951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1901791786710213 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35148924824 / 1000000000000) (-35148914293 / 1000000000000), orderedInterval (10212529398 / 1000000000000) (10212539929 / 1000000000000)))) (orderedInterval (-11894992770 / 1000000000000) (-11894978215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1585515719998197 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38855235333 / 1000000000000) (38855235341 / 1000000000000), orderedInterval (9767218463 / 1000000000000) (9767218470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1400851222486137 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32325950887 / 1000000000000) (-32325903995 / 1000000000000), orderedInterval (27846172059 / 1000000000000) (27846218951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (406021285075563 / 800000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20758266625 / 1000000000000) (-20758264571 / 1000000000000), orderedInterval (28716303309 / 1000000000000) (28716305363 / 1000000000000)))) (orderedInterval (-1669711193 / 1000000000000) (-1669705184 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate403_chunkChecks3_2 :
    compactCertificate403.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1123076242248561 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44194511459 / 1000000000000) (-44194500811 / 1000000000000), orderedInterval (17805999939 / 1000000000000) (17806010587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (952044168282921 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1803213063 / 1000000000000) (1803213065 / 1000000000000), orderedInterval (51682798270 / 1000000000000) (51682798272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (595745035683363 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57526347623 / 1000000000000) (-57526330749 / 1000000000000), orderedInterval (31260001261 / 1000000000000) (31260018135 / 1000000000000)))) (orderedInterval (4815454985 / 1000000000000) (4815456961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (320393661549021 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63900256994 / 1000000000000) (-63900167801 / 1000000000000), orderedInterval (62565758239 / 1000000000000) (62565847432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (869931116550063 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53959272166 / 1000000000000) (-53959272139 / 1000000000000), orderedInterval (-3826708656 / 1000000000000) (-3826708630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1187816566950351 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30257458205 / 1000000000000) (30257473472 / 1000000000000), orderedInterval (-35098323347 / 1000000000000) (-35098308080 / 1000000000000)))) (orderedInterval (-3426590124 / 1000000000000) (-3426588565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (502254964316637 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45018020659 / 1000000000000) (45018020660 / 1000000000000), orderedInterval (54988468024 / 1000000000000) (54988468025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2041638545585277 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27327949023 / 1000000000000) (27327977082 / 1000000000000), orderedInterval (-22397625623 / 1000000000000) (-22397597564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1363719930624243 / 4000000000000) 3 (IntervalRat.scale (549 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28447515588 / 1000000000000) (28447528678 / 1000000000000), orderedInterval (-32569289012 / 1000000000000) (-32569275922 / 1000000000000)))) (orderedInterval (-23517944765 / 1000000000000) (-23517925090 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate403_chunkChecks3 :
    compactCertificate403.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate403.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate403_chunkChecks3_0
    compactCertificate403_chunkChecks3_1 compactCertificate403_chunkChecks3_2

theorem compactCertificate403_chunkChecks4_0 :
    compactCertificate403.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (549 / 2) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44438823121 / 1000000000000) (-44438811256 / 1000000000000), orderedInterval (18638592502 / 1000000000000) (18638604366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (808781830397649 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52757549309 / 1000000000000) (52757554327 / 1000000000000), orderedInterval (-19239879711 / 1000000000000) (-19239874693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (261543426479217 / 800000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36859633453 / 1000000000000) (36859633454 / 1000000000000), orderedInterval (24205472051 / 1000000000000) (24205472052 / 1000000000000)))) (orderedInterval (-13045854736 / 1000000000000) (-13045849951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (236000520979443 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9661818101 / 1000000000000) (-9661818099 / 1000000000000), orderedInterval (-103345258435 / 1000000000000) (-103345258432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (633930595570071 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51699602181 / 1000000000000) (51699655916 / 1000000000000), orderedInterval (-36825236557 / 1000000000000) (-36825182822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1721244884035707 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24723950087 / 1000000000000) (-24723950086 / 1000000000000), orderedInterval (-29435942250 / 1000000000000) (-29435942249 / 1000000000000)))) (orderedInterval (10880850037 / 1000000000000) (10880850378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1267861191140691 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19470995785 / 1000000000000) (-19470995784 / 1000000000000), orderedInterval (-40334691532 / 1000000000000) (-40334691531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2172501761021343 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13806310381 / 1000000000000) (-13806310380 / 1000000000000), orderedInterval (-31316628478 / 1000000000000) (-31316628477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1600254964316637 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38158965328 / 1000000000000) (-38158957067 / 1000000000000), orderedInterval (11674745434 / 1000000000000) (11674753695 / 1000000000000)))) (orderedInterval (2426496874 / 1000000000000) (2426497941 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate403_chunkChecks4_1 :
    compactCertificate403.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2455202639294451 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29606389141 / 1000000000000) (-29606326274 / 1000000000000), orderedInterval (12698470594 / 1000000000000) (12698533462 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1417511904711579 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6880276740 / 1000000000000) (-6880276739 / 1000000000000), orderedInterval (-41812610804 / 1000000000000) (-41812610803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2515399749868311 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30795146607 / 1000000000000) (30795146647 / 1000000000000), orderedInterval (7976407848 / 1000000000000) (7976407888 / 1000000000000)))) (orderedInterval (250543543026 / 1000000000000) (250543825710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2350212735400659 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24957340946 / 1000000000000) (-24957340945 / 1000000000000), orderedInterval (-21441313031 / 1000000000000) (-21441313030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1677222704353347 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30097274242 / 1000000000000) (-30097232425 / 1000000000000), orderedInterval (24783118133 / 1000000000000) (24783159951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1901791786710213 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35148924824 / 1000000000000) (-35148914293 / 1000000000000), orderedInterval (10212529398 / 1000000000000) (10212539929 / 1000000000000)))) (orderedInterval (-4350423415 / 1000000000000) (-4350401042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1585515719998197 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38855235333 / 1000000000000) (38855235341 / 1000000000000), orderedInterval (9767218463 / 1000000000000) (9767218470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1400851222486137 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32325950887 / 1000000000000) (-32325903995 / 1000000000000), orderedInterval (27846172059 / 1000000000000) (27846218951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (406021285075563 / 800000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20758266625 / 1000000000000) (-20758264571 / 1000000000000), orderedInterval (28716303309 / 1000000000000) (28716305363 / 1000000000000)))) (orderedInterval (653182777 / 1000000000000) (653190683 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate403_chunkChecks4_2 :
    compactCertificate403.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1123076242248561 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44194511459 / 1000000000000) (-44194500811 / 1000000000000), orderedInterval (17805999939 / 1000000000000) (17806010587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (952044168282921 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1803213063 / 1000000000000) (1803213065 / 1000000000000), orderedInterval (51682798270 / 1000000000000) (51682798272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (595745035683363 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57526347623 / 1000000000000) (-57526330749 / 1000000000000), orderedInterval (31260001261 / 1000000000000) (31260018135 / 1000000000000)))) (orderedInterval (7479186140 / 1000000000000) (7479188124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (320393661549021 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63900256994 / 1000000000000) (-63900167801 / 1000000000000), orderedInterval (62565758239 / 1000000000000) (62565847432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (869931116550063 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-53959272166 / 1000000000000) (-53959272139 / 1000000000000), orderedInterval (-3826708656 / 1000000000000) (-3826708630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1187816566950351 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30257458205 / 1000000000000) (30257473472 / 1000000000000), orderedInterval (-35098323347 / 1000000000000) (-35098308080 / 1000000000000)))) (orderedInterval (-2660018855 / 1000000000000) (-2660017197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (502254964316637 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45018020659 / 1000000000000) (45018020660 / 1000000000000), orderedInterval (54988468024 / 1000000000000) (54988468025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2041638545585277 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27327949023 / 1000000000000) (27327977082 / 1000000000000), orderedInterval (-22397625623 / 1000000000000) (-22397597564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1363719930624243 / 4000000000000) 4 (IntervalRat.scale (549 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28447515588 / 1000000000000) (28447528678 / 1000000000000), orderedInterval (-32569289012 / 1000000000000) (-32569275922 / 1000000000000)))) (orderedInterval (-39109113420 / 1000000000000) (-39109079741 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate403_chunkChecks4 :
    compactCertificate403.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate403.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate403_chunkChecks4_0
    compactCertificate403_chunkChecks4_1 compactCertificate403_chunkChecks4_2

theorem compactCertificate403_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate403.chunkCheck r b = true :=
  compactCertificate403.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate403_chunkChecks0
    · exact compactCertificate403_chunkChecks1
    · exact compactCertificate403_chunkChecks2
    · exact compactCertificate403_chunkChecks3
    · exact compactCertificate403_chunkChecks4)

theorem compactCertificate403_coefficient0 :
    compactCertificate403.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate403_coefficient1 :
    compactCertificate403.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate403_coefficient2 :
    compactCertificate403.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate403_coefficient3 :
    compactCertificate403.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate403_coefficient4 :
    compactCertificate403.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate403_coefficients : ∀ r : Fin 5,
    compactCertificate403.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate403_coefficient0
  · exact compactCertificate403_coefficient1
  · exact compactCertificate403_coefficient2
  · exact compactCertificate403_coefficient3
  · exact compactCertificate403_coefficient4

theorem compactCertificate403_lower : (1 : ℚ) ≤ compactCertificate403.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate403, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate403_proves {t : ℝ} (ht : t ∈ compactCertificate403.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate403.proves compactCertificate403_states compactCertificate403_chunks
    compactCertificate403_coefficients compactCertificate403_lower ht

end Erdos232
