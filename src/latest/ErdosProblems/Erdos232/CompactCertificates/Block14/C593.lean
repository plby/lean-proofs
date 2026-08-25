/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate593 : CompactCertificate where
  left := 464
  right := 465
  center := 929 / 2
  grid := fun i =>
    match i.val with
    | 0 => 148
    | 1 => 109
    | 2 => 176
    | 3 => 32
    | 4 => 85
    | 5 => 232
    | 6 => 171
    | 7 => 293
    | 8 => 216
    | 9 => 331
    | 10 => 191
    | 11 => 339
    | 12 => 317
    | 13 => 226
    | 14 => 256
    | 15 => 214
    | 16 => 189
    | 17 => 274
    | 18 => 151
    | 19 => 128
    | 20 => 80
    | 21 => 43
    | 22 => 117
    | 23 => 160
    | 24 => 68
    | 25 => 275
    | _ => 184
  point := fun i =>
    match i.val with
    | 0 => 929 / 2
    | 1 => 1368594390600029 / 4000000000000
    | 2 => 442575306373757 / 800000000000
    | 3 => 399352429854103 / 4000000000000
    | 4 => 1072716800154091 / 4000000000000
    | 5 => 2912634785554047 / 4000000000000
    | 6 => 2145433600309111 / 4000000000000
    | 7 => 3676237041874003 / 4000000000000
    | 8 => 2707899566211577 / 4000000000000
    | 9 => 4154614302194071 / 4000000000000
    | 10 => 2398667685750559 / 4000000000000
    | 11 => 4256477900961131 / 4000000000000
    | 12 => 3976953790869239 / 4000000000000
    | 13 => 2838141880408487 / 4000000000000
    | 14 => 3218150400462273 / 4000000000000
    | 15 => 2682958294860337 / 4000000000000
    | 16 => 2370475019471077 / 4000000000000
    | 17 => 687056054344623 / 800000000000
    | 18 => 1900433204096381 / 4000000000000
    | 19 => 1611018273833941 / 4000000000000
    | 20 => 1008100433788423 / 4000000000000
    | 21 => 542159766082041 / 4000000000000
    | 22 => 1472069230009123 / 4000000000000
    | 23 => 2009984682507971 / 4000000000000
    | 24 => 849899566211577 / 4000000000000
    | 25 => 3454794551637017 / 4000000000000
    | _ => 2307642651274903 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (11975923170 / 1000000000000) (11975923171 / 1000000000000), orderedInterval (35017472494 / 1000000000000) (35017472495 / 1000000000000))
    | 1 => (orderedInterval (-20681328960 / 1000000000000) (-20681328959 / 1000000000000), orderedInterval (-37823926146 / 1000000000000) (-37823926145 / 1000000000000))
    | 2 => (orderedInterval (29982142768 / 1000000000000) (29982142769 / 1000000000000), orderedInterval (15841928932 / 1000000000000) (15841928934 / 1000000000000))
    | 3 => (orderedInterval (7279525225 / 1000000000000) (7279525227 / 1000000000000), orderedInterval (79484660778 / 1000000000000) (79484660780 / 1000000000000))
    | 4 => (orderedInterval (-45633897213 / 1000000000000) (-45633889324 / 1000000000000), orderedInterval (17155644075 / 1000000000000) (17155651964 / 1000000000000))
    | 5 => (orderedInterval (2787910048 / 1000000000000) (2787910049 / 1000000000000), orderedInterval (29434710516 / 1000000000000) (29434710517 / 1000000000000))
    | 6 => (orderedInterval (2367680756 / 1000000000000) (2367680758 / 1000000000000), orderedInterval (-34372607321 / 1000000000000) (-34372607320 / 1000000000000))
    | 7 => (orderedInterval (15762367777 / 1000000000000) (15762367969 / 1000000000000), orderedInterval (-21085437155 / 1000000000000) (-21085436963 / 1000000000000))
    | 8 => (orderedInterval (-22502734649 / 1000000000000) (-22502727818 / 1000000000000), orderedInterval (20849669879 / 1000000000000) (20849676709 / 1000000000000))
    | 9 => (orderedInterval (10282694914 / 1000000000000) (10282694917 / 1000000000000), orderedInterval (-22525921319 / 1000000000000) (-22525921316 / 1000000000000))
    | 10 => (orderedInterval (-12925351587 / 1000000000000) (-12925351586 / 1000000000000), orderedInterval (-29898382576 / 1000000000000) (-29898382575 / 1000000000000))
    | 11 => (orderedInterval (2323885062 / 1000000000000) (2323885063 / 1000000000000), orderedInterval (-24349794132 / 1000000000000) (-24349794131 / 1000000000000))
    | 12 => (orderedInterval (19195683843 / 1000000000000) (19195685640 / 1000000000000), orderedInterval (-16497062277 / 1000000000000) (-16497060480 / 1000000000000))
    | 13 => (orderedInterval (9443876150 / 1000000000000) (9443876151 / 1000000000000), orderedInterval (28419529789 / 1000000000000) (28419529790 / 1000000000000))
    | 14 => (orderedInterval (24744360281 / 1000000000000) (24744360285 / 1000000000000), orderedInterval (13363825590 / 1000000000000) (13363825594 / 1000000000000))
    | 15 => (orderedInterval (-21579761896 / 1000000000000) (-21579757616 / 1000000000000), orderedInterval (22003468154 / 1000000000000) (22003472435 / 1000000000000))
    | 16 => (orderedInterval (11456098937 / 1000000000000) (11456098972 / 1000000000000), orderedInterval (-30718076969 / 1000000000000) (-30718076935 / 1000000000000))
    | 17 => (orderedInterval (-25286890556 / 1000000000000) (-25286802598 / 1000000000000), orderedInterval (10106645989 / 1000000000000) (10106733947 / 1000000000000))
    | 18 => (orderedInterval (-36544034678 / 1000000000000) (-36544034466 / 1000000000000), orderedInterval (-2078010633 / 1000000000000) (-2078010421 / 1000000000000))
    | 19 => (orderedInterval (39280923361 / 1000000000000) (39280923393 / 1000000000000), orderedInterval (6089003816 / 1000000000000) (6089003847 / 1000000000000))
    | 20 => (orderedInterval (50064095145 / 1000000000000) (50064095173 / 1000000000000), orderedInterval (4327722708 / 1000000000000) (4327722736 / 1000000000000))
    | 21 => (orderedInterval (-64727132988 / 1000000000000) (-64727132987 / 1000000000000), orderedInterval (-22284318251 / 1000000000000) (-22284318250 / 1000000000000))
    | 22 => (orderedInterval (-39282679152 / 1000000000000) (-39282679150 / 1000000000000), orderedInterval (-13611677623 / 1000000000000) (-13611677621 / 1000000000000))
    | 23 => (orderedInterval (20868941320 / 1000000000000) (20868941321 / 1000000000000), orderedInterval (28813279875 / 1000000000000) (28813279876 / 1000000000000))
    | 24 => (orderedInterval (-19722440802 / 1000000000000) (-19722440231 / 1000000000000), orderedInterval (51107582403 / 1000000000000) (51107582974 / 1000000000000))
    | 25 => (orderedInterval (-14095855234 / 1000000000000) (-14095855233 / 1000000000000), orderedInterval (-23195125310 / 1000000000000) (-23195125309 / 1000000000000))
    | _ => (orderedInterval (-11615201232 / 1000000000000) (-11615201193 / 1000000000000), orderedInterval (31132171876 / 1000000000000) (31132171916 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (6313513140 / 1000000000000) (6313513173 / 1000000000000)
      | 1 => orderedInterval (-1943342504 / 1000000000000) (-1943342160 / 1000000000000)
      | 2 => orderedInterval (-1030021205 / 1000000000000) (-1030021008 / 1000000000000)
      | 3 => orderedInterval (-2454419061 / 1000000000000) (-2454418877 / 1000000000000)
      | 4 => orderedInterval (421277888 / 1000000000000) (421277976 / 1000000000000)
      | 5 => orderedInterval (-1552234748 / 1000000000000) (-1552232400 / 1000000000000)
      | 6 => orderedInterval (5249666502 / 1000000000000) (5249666655 / 1000000000000)
      | 7 => orderedInterval (487022696 / 1000000000000) (487022752 / 1000000000000)
      | _ => orderedInterval (3207854118 / 1000000000000) (3207854258 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14727269981 / 1000000000000) (14727270018 / 1000000000000)
      | 1 => orderedInterval (-3103955058 / 1000000000000) (-3103954828 / 1000000000000)
      | 2 => orderedInterval (2021190945 / 1000000000000) (2021191243 / 1000000000000)
      | 3 => orderedInterval (-1839639215 / 1000000000000) (-1839638832 / 1000000000000)
      | 4 => orderedInterval (4625458715 / 1000000000000) (4625458875 / 1000000000000)
      | 5 => orderedInterval (3088105377 / 1000000000000) (3088109680 / 1000000000000)
      | 6 => orderedInterval (117464332 / 1000000000000) (117464477 / 1000000000000)
      | 7 => orderedInterval (-2024116983 / 1000000000000) (-2024116933 / 1000000000000)
      | _ => orderedInterval (-3603079265 / 1000000000000) (-3603079073 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-7169635968 / 1000000000000) (-7169635926 / 1000000000000)
      | 1 => orderedInterval (1052763125 / 1000000000000) (1052763309 / 1000000000000)
      | 2 => orderedInterval (3054131911 / 1000000000000) (3054132366 / 1000000000000)
      | 3 => orderedInterval (9001857869 / 1000000000000) (9001858690 / 1000000000000)
      | 4 => orderedInterval (-130369501 / 1000000000000) (-130369203 / 1000000000000)
      | 5 => orderedInterval (3793351955 / 1000000000000) (3793359865 / 1000000000000)
      | 6 => orderedInterval (-4921607390 / 1000000000000) (-4921607250 / 1000000000000)
      | 7 => orderedInterval (1214900187 / 1000000000000) (1214900237 / 1000000000000)
      | _ => orderedInterval (-7296273308 / 1000000000000) (-7296273029 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15293850721 / 1000000000000) (-15293850672 / 1000000000000)
      | 1 => orderedInterval (7946699891 / 1000000000000) (7946700078 / 1000000000000)
      | 2 => orderedInterval (-6604116358 / 1000000000000) (-6604115653 / 1000000000000)
      | 3 => orderedInterval (1614088631 / 1000000000000) (1614090430 / 1000000000000)
      | 4 => orderedInterval (-12147506955 / 1000000000000) (-12147506384 / 1000000000000)
      | 5 => orderedInterval (-6059343229 / 1000000000000) (-6059328678 / 1000000000000)
      | 6 => orderedInterval (-142793819 / 1000000000000) (-142793681 / 1000000000000)
      | 7 => orderedInterval (2629222708 / 1000000000000) (2629222760 / 1000000000000)
      | _ => orderedInterval (-961076113 / 1000000000000) (-961075686 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (8295954462 / 1000000000000) (8295954520 / 1000000000000)
      | 1 => orderedInterval (-1416378566 / 1000000000000) (-1416378331 / 1000000000000)
      | 2 => orderedInterval (-9876415113 / 1000000000000) (-9876414004 / 1000000000000)
      | 3 => orderedInterval (-39245756070 / 1000000000000) (-39245752073 / 1000000000000)
      | 4 => orderedInterval (-3486595920 / 1000000000000) (-3486594800 / 1000000000000)
      | 5 => orderedInterval (-10360365506 / 1000000000000) (-10360338673 / 1000000000000)
      | 6 => orderedInterval (5280645617 / 1000000000000) (5280645754 / 1000000000000)
      | 7 => orderedInterval (-1841961416 / 1000000000000) (-1841961362 / 1000000000000)
      | _ => orderedInterval (18900781495 / 1000000000000) (18900782174 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (8699316826 / 1000000000000) (8699320369 / 1000000000000)
    | 1 => orderedInterval (14008698829 / 1000000000000) (14008704627 / 1000000000000)
    | 2 => orderedInterval (-1400881120 / 1000000000000) (-1400870941 / 1000000000000)
    | 3 => orderedInterval (-29018675965 / 1000000000000) (-29018657486 / 1000000000000)
    | _ => orderedInterval (-33750091017 / 1000000000000) (-33750056795 / 1000000000000)

theorem compactCertificate593_stateChecks0 :
    compactCertificate593.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (929 / 2)) (orderedInterval (11975923170 / 1000000000000) (11975923171 / 1000000000000), orderedInterval (35017472494 / 1000000000000) (35017472495 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1368594390600029 / 4000000000000)) (orderedInterval (-20681328960 / 1000000000000) (-20681328959 / 1000000000000), orderedInterval (-37823926146 / 1000000000000) (-37823926145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (442575306373757 / 800000000000)) (orderedInterval (29982142768 / 1000000000000) (29982142769 / 1000000000000), orderedInterval (15841928932 / 1000000000000) (15841928934 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_stateChecks1 :
    compactCertificate593.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (399352429854103 / 4000000000000)) (orderedInterval (7279525225 / 1000000000000) (7279525227 / 1000000000000), orderedInterval (79484660778 / 1000000000000) (79484660780 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1072716800154091 / 4000000000000)) (orderedInterval (-45633897213 / 1000000000000) (-45633889324 / 1000000000000), orderedInterval (17155644075 / 1000000000000) (17155651964 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2912634785554047 / 4000000000000)) (orderedInterval (2787910048 / 1000000000000) (2787910049 / 1000000000000), orderedInterval (29434710516 / 1000000000000) (29434710517 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_stateChecks2 :
    compactCertificate593.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2145433600309111 / 4000000000000)) (orderedInterval (2367680756 / 1000000000000) (2367680758 / 1000000000000), orderedInterval (-34372607321 / 1000000000000) (-34372607320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (3676237041874003 / 4000000000000)) (orderedInterval (15762367777 / 1000000000000) (15762367969 / 1000000000000), orderedInterval (-21085437155 / 1000000000000) (-21085436963 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2707899566211577 / 4000000000000)) (orderedInterval (-22502734649 / 1000000000000) (-22502727818 / 1000000000000), orderedInterval (20849669879 / 1000000000000) (20849676709 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_stateChecks3 :
    compactCertificate593.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 331 12 (4154614302194071 / 4000000000000)) (orderedInterval (10282694914 / 1000000000000) (10282694917 / 1000000000000), orderedInterval (-22525921319 / 1000000000000) (-22525921316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2398667685750559 / 4000000000000)) (orderedInterval (-12925351587 / 1000000000000) (-12925351586 / 1000000000000), orderedInterval (-29898382576 / 1000000000000) (-29898382575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 339 12 (4256477900961131 / 4000000000000)) (orderedInterval (2323885062 / 1000000000000) (2323885063 / 1000000000000), orderedInterval (-24349794132 / 1000000000000) (-24349794131 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_stateChecks4 :
    compactCertificate593.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 317 12 (3976953790869239 / 4000000000000)) (orderedInterval (19195683843 / 1000000000000) (19195685640 / 1000000000000), orderedInterval (-16497062277 / 1000000000000) (-16497060480 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2838141880408487 / 4000000000000)) (orderedInterval (9443876150 / 1000000000000) (9443876151 / 1000000000000), orderedInterval (28419529789 / 1000000000000) (28419529790 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3218150400462273 / 4000000000000)) (orderedInterval (24744360281 / 1000000000000) (24744360285 / 1000000000000), orderedInterval (13363825590 / 1000000000000) (13363825594 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_stateChecks5 :
    compactCertificate593.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2682958294860337 / 4000000000000)) (orderedInterval (-21579761896 / 1000000000000) (-21579757616 / 1000000000000), orderedInterval (22003468154 / 1000000000000) (22003472435 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2370475019471077 / 4000000000000)) (orderedInterval (11456098937 / 1000000000000) (11456098972 / 1000000000000), orderedInterval (-30718076969 / 1000000000000) (-30718076935 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (687056054344623 / 800000000000)) (orderedInterval (-25286890556 / 1000000000000) (-25286802598 / 1000000000000), orderedInterval (10106645989 / 1000000000000) (10106733947 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_stateChecks6 :
    compactCertificate593.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1900433204096381 / 4000000000000)) (orderedInterval (-36544034678 / 1000000000000) (-36544034466 / 1000000000000), orderedInterval (-2078010633 / 1000000000000) (-2078010421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1611018273833941 / 4000000000000)) (orderedInterval (39280923361 / 1000000000000) (39280923393 / 1000000000000), orderedInterval (6089003816 / 1000000000000) (6089003847 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1008100433788423 / 4000000000000)) (orderedInterval (50064095145 / 1000000000000) (50064095173 / 1000000000000), orderedInterval (4327722708 / 1000000000000) (4327722736 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_stateChecks7 :
    compactCertificate593.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (542159766082041 / 4000000000000)) (orderedInterval (-64727132988 / 1000000000000) (-64727132987 / 1000000000000), orderedInterval (-22284318251 / 1000000000000) (-22284318250 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1472069230009123 / 4000000000000)) (orderedInterval (-39282679152 / 1000000000000) (-39282679150 / 1000000000000), orderedInterval (-13611677623 / 1000000000000) (-13611677621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2009984682507971 / 4000000000000)) (orderedInterval (20868941320 / 1000000000000) (20868941321 / 1000000000000), orderedInterval (28813279875 / 1000000000000) (28813279876 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_stateChecks8 :
    compactCertificate593.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (849899566211577 / 4000000000000)) (orderedInterval (-19722440802 / 1000000000000) (-19722440231 / 1000000000000), orderedInterval (51107582403 / 1000000000000) (51107582974 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (3454794551637017 / 4000000000000)) (orderedInterval (-14095855234 / 1000000000000) (-14095855233 / 1000000000000), orderedInterval (-23195125310 / 1000000000000) (-23195125309 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2307642651274903 / 4000000000000)) (orderedInterval (-11615201232 / 1000000000000) (-11615201193 / 1000000000000), orderedInterval (31132171876 / 1000000000000) (31132171916 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_states : ∀ j,
    BesselStateValid (compactCertificate593.point j) (compactCertificate593.state j) :=
  compactCertificate593.statesValid_of_checks3 compactCertificate593_stateChecks0
    compactCertificate593_stateChecks1 compactCertificate593_stateChecks2
    compactCertificate593_stateChecks3 compactCertificate593_stateChecks4
    compactCertificate593_stateChecks5 compactCertificate593_stateChecks6
    compactCertificate593_stateChecks7 compactCertificate593_stateChecks8

theorem compactCertificate593_chunkChecks0_0 :
    compactCertificate593.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (929 / 2) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11975923170 / 1000000000000) (11975923171 / 1000000000000), orderedInterval (35017472494 / 1000000000000) (35017472495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1368594390600029 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20681328960 / 1000000000000) (-20681328959 / 1000000000000), orderedInterval (-37823926146 / 1000000000000) (-37823926145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (442575306373757 / 800000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29982142768 / 1000000000000) (29982142769 / 1000000000000), orderedInterval (15841928932 / 1000000000000) (15841928934 / 1000000000000)))) (orderedInterval (6313513140 / 1000000000000) (6313513173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (399352429854103 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7279525225 / 1000000000000) (7279525227 / 1000000000000), orderedInterval (79484660778 / 1000000000000) (79484660780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1072716800154091 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45633897213 / 1000000000000) (-45633889324 / 1000000000000), orderedInterval (17155644075 / 1000000000000) (17155651964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2912634785554047 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2787910048 / 1000000000000) (2787910049 / 1000000000000), orderedInterval (29434710516 / 1000000000000) (29434710517 / 1000000000000)))) (orderedInterval (-1943342504 / 1000000000000) (-1943342160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2145433600309111 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2367680756 / 1000000000000) (2367680758 / 1000000000000), orderedInterval (-34372607321 / 1000000000000) (-34372607320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3676237041874003 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15762367777 / 1000000000000) (15762367969 / 1000000000000), orderedInterval (-21085437155 / 1000000000000) (-21085436963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2707899566211577 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22502734649 / 1000000000000) (-22502727818 / 1000000000000), orderedInterval (20849669879 / 1000000000000) (20849676709 / 1000000000000)))) (orderedInterval (-1030021205 / 1000000000000) (-1030021008 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks0_1 :
    compactCertificate593.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4154614302194071 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10282694914 / 1000000000000) (10282694917 / 1000000000000), orderedInterval (-22525921319 / 1000000000000) (-22525921316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2398667685750559 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12925351587 / 1000000000000) (-12925351586 / 1000000000000), orderedInterval (-29898382576 / 1000000000000) (-29898382575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4256477900961131 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2323885062 / 1000000000000) (2323885063 / 1000000000000), orderedInterval (-24349794132 / 1000000000000) (-24349794131 / 1000000000000)))) (orderedInterval (-2454419061 / 1000000000000) (-2454418877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3976953790869239 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (19195683843 / 1000000000000) (19195685640 / 1000000000000), orderedInterval (-16497062277 / 1000000000000) (-16497060480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2838141880408487 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9443876150 / 1000000000000) (9443876151 / 1000000000000), orderedInterval (28419529789 / 1000000000000) (28419529790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3218150400462273 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24744360281 / 1000000000000) (24744360285 / 1000000000000), orderedInterval (13363825590 / 1000000000000) (13363825594 / 1000000000000)))) (orderedInterval (421277888 / 1000000000000) (421277976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2682958294860337 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21579761896 / 1000000000000) (-21579757616 / 1000000000000), orderedInterval (22003468154 / 1000000000000) (22003472435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2370475019471077 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11456098937 / 1000000000000) (11456098972 / 1000000000000), orderedInterval (-30718076969 / 1000000000000) (-30718076935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (687056054344623 / 800000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25286890556 / 1000000000000) (-25286802598 / 1000000000000), orderedInterval (10106645989 / 1000000000000) (10106733947 / 1000000000000)))) (orderedInterval (-1552234748 / 1000000000000) (-1552232400 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks0_2 :
    compactCertificate593.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1900433204096381 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36544034678 / 1000000000000) (-36544034466 / 1000000000000), orderedInterval (-2078010633 / 1000000000000) (-2078010421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1611018273833941 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39280923361 / 1000000000000) (39280923393 / 1000000000000), orderedInterval (6089003816 / 1000000000000) (6089003847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1008100433788423 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50064095145 / 1000000000000) (50064095173 / 1000000000000), orderedInterval (4327722708 / 1000000000000) (4327722736 / 1000000000000)))) (orderedInterval (5249666502 / 1000000000000) (5249666655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (542159766082041 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64727132988 / 1000000000000) (-64727132987 / 1000000000000), orderedInterval (-22284318251 / 1000000000000) (-22284318250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1472069230009123 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39282679152 / 1000000000000) (-39282679150 / 1000000000000), orderedInterval (-13611677623 / 1000000000000) (-13611677621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2009984682507971 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20868941320 / 1000000000000) (20868941321 / 1000000000000), orderedInterval (28813279875 / 1000000000000) (28813279876 / 1000000000000)))) (orderedInterval (487022696 / 1000000000000) (487022752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (849899566211577 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19722440802 / 1000000000000) (-19722440231 / 1000000000000), orderedInterval (51107582403 / 1000000000000) (51107582974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3454794551637017 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14095855234 / 1000000000000) (-14095855233 / 1000000000000), orderedInterval (-23195125310 / 1000000000000) (-23195125309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2307642651274903 / 4000000000000) 0 (IntervalRat.scale (929 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11615201232 / 1000000000000) (-11615201193 / 1000000000000), orderedInterval (31132171876 / 1000000000000) (31132171916 / 1000000000000)))) (orderedInterval (3207854118 / 1000000000000) (3207854258 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks0 :
    compactCertificate593.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate593.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate593_chunkChecks0_0
    compactCertificate593_chunkChecks0_1 compactCertificate593_chunkChecks0_2

theorem compactCertificate593_chunkChecks1_0 :
    compactCertificate593.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (929 / 2) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11975923170 / 1000000000000) (11975923171 / 1000000000000), orderedInterval (35017472494 / 1000000000000) (35017472495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1368594390600029 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20681328960 / 1000000000000) (-20681328959 / 1000000000000), orderedInterval (-37823926146 / 1000000000000) (-37823926145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (442575306373757 / 800000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29982142768 / 1000000000000) (29982142769 / 1000000000000), orderedInterval (15841928932 / 1000000000000) (15841928934 / 1000000000000)))) (orderedInterval (14727269981 / 1000000000000) (14727270018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (399352429854103 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7279525225 / 1000000000000) (7279525227 / 1000000000000), orderedInterval (79484660778 / 1000000000000) (79484660780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1072716800154091 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45633897213 / 1000000000000) (-45633889324 / 1000000000000), orderedInterval (17155644075 / 1000000000000) (17155651964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2912634785554047 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2787910048 / 1000000000000) (2787910049 / 1000000000000), orderedInterval (29434710516 / 1000000000000) (29434710517 / 1000000000000)))) (orderedInterval (-3103955058 / 1000000000000) (-3103954828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2145433600309111 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2367680756 / 1000000000000) (2367680758 / 1000000000000), orderedInterval (-34372607321 / 1000000000000) (-34372607320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3676237041874003 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15762367777 / 1000000000000) (15762367969 / 1000000000000), orderedInterval (-21085437155 / 1000000000000) (-21085436963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2707899566211577 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22502734649 / 1000000000000) (-22502727818 / 1000000000000), orderedInterval (20849669879 / 1000000000000) (20849676709 / 1000000000000)))) (orderedInterval (2021190945 / 1000000000000) (2021191243 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks1_1 :
    compactCertificate593.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4154614302194071 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10282694914 / 1000000000000) (10282694917 / 1000000000000), orderedInterval (-22525921319 / 1000000000000) (-22525921316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2398667685750559 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12925351587 / 1000000000000) (-12925351586 / 1000000000000), orderedInterval (-29898382576 / 1000000000000) (-29898382575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4256477900961131 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2323885062 / 1000000000000) (2323885063 / 1000000000000), orderedInterval (-24349794132 / 1000000000000) (-24349794131 / 1000000000000)))) (orderedInterval (-1839639215 / 1000000000000) (-1839638832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3976953790869239 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (19195683843 / 1000000000000) (19195685640 / 1000000000000), orderedInterval (-16497062277 / 1000000000000) (-16497060480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2838141880408487 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9443876150 / 1000000000000) (9443876151 / 1000000000000), orderedInterval (28419529789 / 1000000000000) (28419529790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3218150400462273 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24744360281 / 1000000000000) (24744360285 / 1000000000000), orderedInterval (13363825590 / 1000000000000) (13363825594 / 1000000000000)))) (orderedInterval (4625458715 / 1000000000000) (4625458875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2682958294860337 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21579761896 / 1000000000000) (-21579757616 / 1000000000000), orderedInterval (22003468154 / 1000000000000) (22003472435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2370475019471077 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11456098937 / 1000000000000) (11456098972 / 1000000000000), orderedInterval (-30718076969 / 1000000000000) (-30718076935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (687056054344623 / 800000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25286890556 / 1000000000000) (-25286802598 / 1000000000000), orderedInterval (10106645989 / 1000000000000) (10106733947 / 1000000000000)))) (orderedInterval (3088105377 / 1000000000000) (3088109680 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks1_2 :
    compactCertificate593.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1900433204096381 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36544034678 / 1000000000000) (-36544034466 / 1000000000000), orderedInterval (-2078010633 / 1000000000000) (-2078010421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1611018273833941 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39280923361 / 1000000000000) (39280923393 / 1000000000000), orderedInterval (6089003816 / 1000000000000) (6089003847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1008100433788423 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50064095145 / 1000000000000) (50064095173 / 1000000000000), orderedInterval (4327722708 / 1000000000000) (4327722736 / 1000000000000)))) (orderedInterval (117464332 / 1000000000000) (117464477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (542159766082041 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64727132988 / 1000000000000) (-64727132987 / 1000000000000), orderedInterval (-22284318251 / 1000000000000) (-22284318250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1472069230009123 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39282679152 / 1000000000000) (-39282679150 / 1000000000000), orderedInterval (-13611677623 / 1000000000000) (-13611677621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2009984682507971 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20868941320 / 1000000000000) (20868941321 / 1000000000000), orderedInterval (28813279875 / 1000000000000) (28813279876 / 1000000000000)))) (orderedInterval (-2024116983 / 1000000000000) (-2024116933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (849899566211577 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19722440802 / 1000000000000) (-19722440231 / 1000000000000), orderedInterval (51107582403 / 1000000000000) (51107582974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3454794551637017 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14095855234 / 1000000000000) (-14095855233 / 1000000000000), orderedInterval (-23195125310 / 1000000000000) (-23195125309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2307642651274903 / 4000000000000) 1 (IntervalRat.scale (929 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11615201232 / 1000000000000) (-11615201193 / 1000000000000), orderedInterval (31132171876 / 1000000000000) (31132171916 / 1000000000000)))) (orderedInterval (-3603079265 / 1000000000000) (-3603079073 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks1 :
    compactCertificate593.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate593.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate593_chunkChecks1_0
    compactCertificate593_chunkChecks1_1 compactCertificate593_chunkChecks1_2

theorem compactCertificate593_chunkChecks2_0 :
    compactCertificate593.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (929 / 2) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11975923170 / 1000000000000) (11975923171 / 1000000000000), orderedInterval (35017472494 / 1000000000000) (35017472495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1368594390600029 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20681328960 / 1000000000000) (-20681328959 / 1000000000000), orderedInterval (-37823926146 / 1000000000000) (-37823926145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (442575306373757 / 800000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29982142768 / 1000000000000) (29982142769 / 1000000000000), orderedInterval (15841928932 / 1000000000000) (15841928934 / 1000000000000)))) (orderedInterval (-7169635968 / 1000000000000) (-7169635926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (399352429854103 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7279525225 / 1000000000000) (7279525227 / 1000000000000), orderedInterval (79484660778 / 1000000000000) (79484660780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1072716800154091 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45633897213 / 1000000000000) (-45633889324 / 1000000000000), orderedInterval (17155644075 / 1000000000000) (17155651964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2912634785554047 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2787910048 / 1000000000000) (2787910049 / 1000000000000), orderedInterval (29434710516 / 1000000000000) (29434710517 / 1000000000000)))) (orderedInterval (1052763125 / 1000000000000) (1052763309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2145433600309111 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2367680756 / 1000000000000) (2367680758 / 1000000000000), orderedInterval (-34372607321 / 1000000000000) (-34372607320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3676237041874003 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15762367777 / 1000000000000) (15762367969 / 1000000000000), orderedInterval (-21085437155 / 1000000000000) (-21085436963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2707899566211577 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22502734649 / 1000000000000) (-22502727818 / 1000000000000), orderedInterval (20849669879 / 1000000000000) (20849676709 / 1000000000000)))) (orderedInterval (3054131911 / 1000000000000) (3054132366 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks2_1 :
    compactCertificate593.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4154614302194071 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10282694914 / 1000000000000) (10282694917 / 1000000000000), orderedInterval (-22525921319 / 1000000000000) (-22525921316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2398667685750559 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12925351587 / 1000000000000) (-12925351586 / 1000000000000), orderedInterval (-29898382576 / 1000000000000) (-29898382575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4256477900961131 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2323885062 / 1000000000000) (2323885063 / 1000000000000), orderedInterval (-24349794132 / 1000000000000) (-24349794131 / 1000000000000)))) (orderedInterval (9001857869 / 1000000000000) (9001858690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3976953790869239 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (19195683843 / 1000000000000) (19195685640 / 1000000000000), orderedInterval (-16497062277 / 1000000000000) (-16497060480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2838141880408487 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9443876150 / 1000000000000) (9443876151 / 1000000000000), orderedInterval (28419529789 / 1000000000000) (28419529790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3218150400462273 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24744360281 / 1000000000000) (24744360285 / 1000000000000), orderedInterval (13363825590 / 1000000000000) (13363825594 / 1000000000000)))) (orderedInterval (-130369501 / 1000000000000) (-130369203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2682958294860337 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21579761896 / 1000000000000) (-21579757616 / 1000000000000), orderedInterval (22003468154 / 1000000000000) (22003472435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2370475019471077 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11456098937 / 1000000000000) (11456098972 / 1000000000000), orderedInterval (-30718076969 / 1000000000000) (-30718076935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (687056054344623 / 800000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25286890556 / 1000000000000) (-25286802598 / 1000000000000), orderedInterval (10106645989 / 1000000000000) (10106733947 / 1000000000000)))) (orderedInterval (3793351955 / 1000000000000) (3793359865 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks2_2 :
    compactCertificate593.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1900433204096381 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36544034678 / 1000000000000) (-36544034466 / 1000000000000), orderedInterval (-2078010633 / 1000000000000) (-2078010421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1611018273833941 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39280923361 / 1000000000000) (39280923393 / 1000000000000), orderedInterval (6089003816 / 1000000000000) (6089003847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1008100433788423 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50064095145 / 1000000000000) (50064095173 / 1000000000000), orderedInterval (4327722708 / 1000000000000) (4327722736 / 1000000000000)))) (orderedInterval (-4921607390 / 1000000000000) (-4921607250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (542159766082041 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64727132988 / 1000000000000) (-64727132987 / 1000000000000), orderedInterval (-22284318251 / 1000000000000) (-22284318250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1472069230009123 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39282679152 / 1000000000000) (-39282679150 / 1000000000000), orderedInterval (-13611677623 / 1000000000000) (-13611677621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2009984682507971 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20868941320 / 1000000000000) (20868941321 / 1000000000000), orderedInterval (28813279875 / 1000000000000) (28813279876 / 1000000000000)))) (orderedInterval (1214900187 / 1000000000000) (1214900237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (849899566211577 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19722440802 / 1000000000000) (-19722440231 / 1000000000000), orderedInterval (51107582403 / 1000000000000) (51107582974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3454794551637017 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14095855234 / 1000000000000) (-14095855233 / 1000000000000), orderedInterval (-23195125310 / 1000000000000) (-23195125309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2307642651274903 / 4000000000000) 2 (IntervalRat.scale (929 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11615201232 / 1000000000000) (-11615201193 / 1000000000000), orderedInterval (31132171876 / 1000000000000) (31132171916 / 1000000000000)))) (orderedInterval (-7296273308 / 1000000000000) (-7296273029 / 1000000000000))) = true
  rfl'

theorem compactCertificate593_chunkChecks2 :
    compactCertificate593.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate593.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate593_chunkChecks2_0
    compactCertificate593_chunkChecks2_1 compactCertificate593_chunkChecks2_2

theorem compactCertificate593_chunkChecks3_0 :
    compactCertificate593.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (929 / 2) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11975923170 / 1000000000000) (11975923171 / 1000000000000), orderedInterval (35017472494 / 1000000000000) (35017472495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1368594390600029 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20681328960 / 1000000000000) (-20681328959 / 1000000000000), orderedInterval (-37823926146 / 1000000000000) (-37823926145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (442575306373757 / 800000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29982142768 / 1000000000000) (29982142769 / 1000000000000), orderedInterval (15841928932 / 1000000000000) (15841928934 / 1000000000000)))) (orderedInterval (-15293850721 / 1000000000000) (-15293850672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (399352429854103 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7279525225 / 1000000000000) (7279525227 / 1000000000000), orderedInterval (79484660778 / 1000000000000) (79484660780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1072716800154091 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45633897213 / 1000000000000) (-45633889324 / 1000000000000), orderedInterval (17155644075 / 1000000000000) (17155651964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2912634785554047 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2787910048 / 1000000000000) (2787910049 / 1000000000000), orderedInterval (29434710516 / 1000000000000) (29434710517 / 1000000000000)))) (orderedInterval (7946699891 / 1000000000000) (7946700078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2145433600309111 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2367680756 / 1000000000000) (2367680758 / 1000000000000), orderedInterval (-34372607321 / 1000000000000) (-34372607320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3676237041874003 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15762367777 / 1000000000000) (15762367969 / 1000000000000), orderedInterval (-21085437155 / 1000000000000) (-21085436963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2707899566211577 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22502734649 / 1000000000000) (-22502727818 / 1000000000000), orderedInterval (20849669879 / 1000000000000) (20849676709 / 1000000000000)))) (orderedInterval (-6604116358 / 1000000000000) (-6604115653 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate593_chunkChecks3_1 :
    compactCertificate593.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4154614302194071 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10282694914 / 1000000000000) (10282694917 / 1000000000000), orderedInterval (-22525921319 / 1000000000000) (-22525921316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2398667685750559 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12925351587 / 1000000000000) (-12925351586 / 1000000000000), orderedInterval (-29898382576 / 1000000000000) (-29898382575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4256477900961131 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2323885062 / 1000000000000) (2323885063 / 1000000000000), orderedInterval (-24349794132 / 1000000000000) (-24349794131 / 1000000000000)))) (orderedInterval (1614088631 / 1000000000000) (1614090430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3976953790869239 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (19195683843 / 1000000000000) (19195685640 / 1000000000000), orderedInterval (-16497062277 / 1000000000000) (-16497060480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2838141880408487 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9443876150 / 1000000000000) (9443876151 / 1000000000000), orderedInterval (28419529789 / 1000000000000) (28419529790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3218150400462273 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24744360281 / 1000000000000) (24744360285 / 1000000000000), orderedInterval (13363825590 / 1000000000000) (13363825594 / 1000000000000)))) (orderedInterval (-12147506955 / 1000000000000) (-12147506384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2682958294860337 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21579761896 / 1000000000000) (-21579757616 / 1000000000000), orderedInterval (22003468154 / 1000000000000) (22003472435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2370475019471077 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11456098937 / 1000000000000) (11456098972 / 1000000000000), orderedInterval (-30718076969 / 1000000000000) (-30718076935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (687056054344623 / 800000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25286890556 / 1000000000000) (-25286802598 / 1000000000000), orderedInterval (10106645989 / 1000000000000) (10106733947 / 1000000000000)))) (orderedInterval (-6059343229 / 1000000000000) (-6059328678 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate593_chunkChecks3_2 :
    compactCertificate593.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1900433204096381 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36544034678 / 1000000000000) (-36544034466 / 1000000000000), orderedInterval (-2078010633 / 1000000000000) (-2078010421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1611018273833941 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39280923361 / 1000000000000) (39280923393 / 1000000000000), orderedInterval (6089003816 / 1000000000000) (6089003847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1008100433788423 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50064095145 / 1000000000000) (50064095173 / 1000000000000), orderedInterval (4327722708 / 1000000000000) (4327722736 / 1000000000000)))) (orderedInterval (-142793819 / 1000000000000) (-142793681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (542159766082041 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64727132988 / 1000000000000) (-64727132987 / 1000000000000), orderedInterval (-22284318251 / 1000000000000) (-22284318250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1472069230009123 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39282679152 / 1000000000000) (-39282679150 / 1000000000000), orderedInterval (-13611677623 / 1000000000000) (-13611677621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2009984682507971 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20868941320 / 1000000000000) (20868941321 / 1000000000000), orderedInterval (28813279875 / 1000000000000) (28813279876 / 1000000000000)))) (orderedInterval (2629222708 / 1000000000000) (2629222760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (849899566211577 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19722440802 / 1000000000000) (-19722440231 / 1000000000000), orderedInterval (51107582403 / 1000000000000) (51107582974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3454794551637017 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14095855234 / 1000000000000) (-14095855233 / 1000000000000), orderedInterval (-23195125310 / 1000000000000) (-23195125309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2307642651274903 / 4000000000000) 3 (IntervalRat.scale (929 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11615201232 / 1000000000000) (-11615201193 / 1000000000000), orderedInterval (31132171876 / 1000000000000) (31132171916 / 1000000000000)))) (orderedInterval (-961076113 / 1000000000000) (-961075686 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate593_chunkChecks3 :
    compactCertificate593.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate593.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate593_chunkChecks3_0
    compactCertificate593_chunkChecks3_1 compactCertificate593_chunkChecks3_2

theorem compactCertificate593_chunkChecks4_0 :
    compactCertificate593.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (929 / 2) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11975923170 / 1000000000000) (11975923171 / 1000000000000), orderedInterval (35017472494 / 1000000000000) (35017472495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1368594390600029 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20681328960 / 1000000000000) (-20681328959 / 1000000000000), orderedInterval (-37823926146 / 1000000000000) (-37823926145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (442575306373757 / 800000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29982142768 / 1000000000000) (29982142769 / 1000000000000), orderedInterval (15841928932 / 1000000000000) (15841928934 / 1000000000000)))) (orderedInterval (8295954462 / 1000000000000) (8295954520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (399352429854103 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7279525225 / 1000000000000) (7279525227 / 1000000000000), orderedInterval (79484660778 / 1000000000000) (79484660780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1072716800154091 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45633897213 / 1000000000000) (-45633889324 / 1000000000000), orderedInterval (17155644075 / 1000000000000) (17155651964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2912634785554047 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2787910048 / 1000000000000) (2787910049 / 1000000000000), orderedInterval (29434710516 / 1000000000000) (29434710517 / 1000000000000)))) (orderedInterval (-1416378566 / 1000000000000) (-1416378331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2145433600309111 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2367680756 / 1000000000000) (2367680758 / 1000000000000), orderedInterval (-34372607321 / 1000000000000) (-34372607320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3676237041874003 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15762367777 / 1000000000000) (15762367969 / 1000000000000), orderedInterval (-21085437155 / 1000000000000) (-21085436963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2707899566211577 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22502734649 / 1000000000000) (-22502727818 / 1000000000000), orderedInterval (20849669879 / 1000000000000) (20849676709 / 1000000000000)))) (orderedInterval (-9876415113 / 1000000000000) (-9876414004 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate593_chunkChecks4_1 :
    compactCertificate593.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4154614302194071 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10282694914 / 1000000000000) (10282694917 / 1000000000000), orderedInterval (-22525921319 / 1000000000000) (-22525921316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2398667685750559 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12925351587 / 1000000000000) (-12925351586 / 1000000000000), orderedInterval (-29898382576 / 1000000000000) (-29898382575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4256477900961131 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2323885062 / 1000000000000) (2323885063 / 1000000000000), orderedInterval (-24349794132 / 1000000000000) (-24349794131 / 1000000000000)))) (orderedInterval (-39245756070 / 1000000000000) (-39245752073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3976953790869239 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (19195683843 / 1000000000000) (19195685640 / 1000000000000), orderedInterval (-16497062277 / 1000000000000) (-16497060480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2838141880408487 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (9443876150 / 1000000000000) (9443876151 / 1000000000000), orderedInterval (28419529789 / 1000000000000) (28419529790 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3218150400462273 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24744360281 / 1000000000000) (24744360285 / 1000000000000), orderedInterval (13363825590 / 1000000000000) (13363825594 / 1000000000000)))) (orderedInterval (-3486595920 / 1000000000000) (-3486594800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2682958294860337 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21579761896 / 1000000000000) (-21579757616 / 1000000000000), orderedInterval (22003468154 / 1000000000000) (22003472435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2370475019471077 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11456098937 / 1000000000000) (11456098972 / 1000000000000), orderedInterval (-30718076969 / 1000000000000) (-30718076935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (687056054344623 / 800000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25286890556 / 1000000000000) (-25286802598 / 1000000000000), orderedInterval (10106645989 / 1000000000000) (10106733947 / 1000000000000)))) (orderedInterval (-10360365506 / 1000000000000) (-10360338673 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate593_chunkChecks4_2 :
    compactCertificate593.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1900433204096381 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36544034678 / 1000000000000) (-36544034466 / 1000000000000), orderedInterval (-2078010633 / 1000000000000) (-2078010421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1611018273833941 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39280923361 / 1000000000000) (39280923393 / 1000000000000), orderedInterval (6089003816 / 1000000000000) (6089003847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1008100433788423 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50064095145 / 1000000000000) (50064095173 / 1000000000000), orderedInterval (4327722708 / 1000000000000) (4327722736 / 1000000000000)))) (orderedInterval (5280645617 / 1000000000000) (5280645754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (542159766082041 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64727132988 / 1000000000000) (-64727132987 / 1000000000000), orderedInterval (-22284318251 / 1000000000000) (-22284318250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1472069230009123 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39282679152 / 1000000000000) (-39282679150 / 1000000000000), orderedInterval (-13611677623 / 1000000000000) (-13611677621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2009984682507971 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20868941320 / 1000000000000) (20868941321 / 1000000000000), orderedInterval (28813279875 / 1000000000000) (28813279876 / 1000000000000)))) (orderedInterval (-1841961416 / 1000000000000) (-1841961362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (849899566211577 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19722440802 / 1000000000000) (-19722440231 / 1000000000000), orderedInterval (51107582403 / 1000000000000) (51107582974 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3454794551637017 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14095855234 / 1000000000000) (-14095855233 / 1000000000000), orderedInterval (-23195125310 / 1000000000000) (-23195125309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2307642651274903 / 4000000000000) 4 (IntervalRat.scale (929 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11615201232 / 1000000000000) (-11615201193 / 1000000000000), orderedInterval (31132171876 / 1000000000000) (31132171916 / 1000000000000)))) (orderedInterval (18900781495 / 1000000000000) (18900782174 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate593_chunkChecks4 :
    compactCertificate593.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate593.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate593_chunkChecks4_0
    compactCertificate593_chunkChecks4_1 compactCertificate593_chunkChecks4_2

theorem compactCertificate593_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate593.chunkCheck r b = true :=
  compactCertificate593.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate593_chunkChecks0
    · exact compactCertificate593_chunkChecks1
    · exact compactCertificate593_chunkChecks2
    · exact compactCertificate593_chunkChecks3
    · exact compactCertificate593_chunkChecks4)

theorem compactCertificate593_coefficient0 :
    compactCertificate593.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate593_coefficient1 :
    compactCertificate593.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate593_coefficient2 :
    compactCertificate593.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate593_coefficient3 :
    compactCertificate593.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate593_coefficient4 :
    compactCertificate593.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate593_coefficients : ∀ r : Fin 5,
    compactCertificate593.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate593_coefficient0
  · exact compactCertificate593_coefficient1
  · exact compactCertificate593_coefficient2
  · exact compactCertificate593_coefficient3
  · exact compactCertificate593_coefficient4

theorem compactCertificate593_lower : (1 : ℚ) ≤ compactCertificate593.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate593, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate593_proves {t : ℝ} (ht : t ∈ compactCertificate593.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate593.proves compactCertificate593_states compactCertificate593_chunks
    compactCertificate593_coefficients compactCertificate593_lower ht

end Erdos232
