/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate626 : CompactCertificate where
  left := 497
  right := 498
  center := 995 / 2
  grid := fun i =>
    match i.val with
    | 0 => 158
    | 1 => 117
    | 2 => 189
    | 3 => 34
    | 4 => 91
    | 5 => 248
    | 6 => 183
    | 7 => 313
    | 8 => 231
    | 9 => 354
    | 10 => 205
    | 11 => 363
    | 12 => 339
    | 13 => 242
    | 14 => 274
    | 15 => 229
    | 16 => 202
    | 17 => 293
    | 18 => 162
    | 19 => 137
    | 20 => 86
    | 21 => 46
    | 22 => 126
    | 23 => 171
    | 24 => 72
    | 25 => 295
    | _ => 197
  point := fun i =>
    match i.val with
    | 0 => 995 / 2
    | 1 => 293164998632299 / 800000000000
    | 2 => 94803537102667 / 160000000000
    | 3 => 85544815436993 / 800000000000
    | 4 => 229785407137421 / 800000000000
    | 5 => 623912080005657 / 800000000000
    | 6 => 459570814275041 / 800000000000
    | 7 => 787482423393893 / 800000000000
    | 8 => 580055988887087 / 800000000000
    | 9 => 889955055044801 / 800000000000
    | 10 => 513815790596729 / 800000000000
    | 11 => 911775137019661 / 800000000000
    | 12 => 851898605363809 / 800000000000
    | 13 => 607955042197297 / 800000000000
    | 14 => 689356221412263 / 800000000000
    | 15 => 574713348414647 / 800000000000
    | 16 => 507776672631587 / 800000000000
    | 17 => 147173471275113 / 160000000000
    | 18 => 407089566862411 / 800000000000
    | 19 => 345094334222771 / 800000000000
    | 20 => 215944011112913 / 800000000000
    | 21 => 116135407373871 / 800000000000
    | 22 => 315330222574613 / 800000000000
    | 23 => 430556460515701 / 800000000000
    | 24 => 182055988887087 / 800000000000
    | 25 => 740047487379727 / 800000000000
    | _ => 494317424761793 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (33691755010 / 1000000000000) (33691776154 / 1000000000000), orderedInterval (-12054775873 / 1000000000000) (-12054754728 / 1000000000000))
    | 1 => (orderedInterval (13310210498 / 1000000000000) (13310210613 / 1000000000000), orderedInterval (-39515910892 / 1000000000000) (-39515910777 / 1000000000000))
    | 2 => (orderedInterval (14367094825 / 1000000000000) (14367094966 / 1000000000000), orderedInterval (-29474141364 / 1000000000000) (-29474141224 / 1000000000000))
    | 3 => (orderedInterval (60493257441 / 1000000000000) (60493257442 / 1000000000000), orderedInterval (47613977036 / 1000000000000) (47613977037 / 1000000000000))
    | 4 => (orderedInterval (-39862729729 / 1000000000000) (-39862671540 / 1000000000000), orderedInterval (25116539057 / 1000000000000) (25116597246 / 1000000000000))
    | 5 => (orderedInterval (28569302764 / 1000000000000) (28569305240 / 1000000000000), orderedInterval (279857704 / 1000000000000) (279860181 / 1000000000000))
    | 6 => (orderedInterval (-11015082709 / 1000000000000) (-11015082708 / 1000000000000), orderedInterval (-31404853128 / 1000000000000) (-31404853127 / 1000000000000))
    | 7 => (orderedInterval (-24646775193 / 1000000000000) (-24646692225 / 1000000000000), orderedInterval (6279668079 / 1000000000000) (6279751047 / 1000000000000))
    | 8 => (orderedInterval (-4349178085 / 1000000000000) (-4349178084 / 1000000000000), orderedInterval (-29307345974 / 1000000000000) (-29307345973 / 1000000000000))
    | 9 => (orderedInterval (21376901602 / 1000000000000) (21376901667 / 1000000000000), orderedInterval (10728149273 / 1000000000000) (10728149338 / 1000000000000))
    | 10 => (orderedInterval (25997761946 / 1000000000000) (25997795610 / 1000000000000), orderedInterval (-17777465137 / 1000000000000) (-17777431474 / 1000000000000))
    | 11 => (orderedInterval (-2502335920 / 1000000000000) (-2502335919 / 1000000000000), orderedInterval (-23500274238 / 1000000000000) (-23500274237 / 1000000000000))
    | 12 => (orderedInterval (-14964611563 / 1000000000000) (-14964611562 / 1000000000000), orderedInterval (-19329379836 / 1000000000000) (-19329379835 / 1000000000000))
    | 13 => (orderedInterval (12943010450 / 1000000000000) (12943010451 / 1000000000000), orderedInterval (25879669351 / 1000000000000) (25879669352 / 1000000000000))
    | 14 => (orderedInterval (27006436295 / 1000000000000) (27006450074 / 1000000000000), orderedInterval (-3089939212 / 1000000000000) (-3089925434 / 1000000000000))
    | 15 => (orderedInterval (7301643315 / 1000000000000) (7301643317 / 1000000000000), orderedInterval (-28864392915 / 1000000000000) (-28864392912 / 1000000000000))
    | 16 => (orderedInterval (24892925581 / 1000000000000) (24892925582 / 1000000000000), orderedInterval (19559306397 / 1000000000000) (19559306398 / 1000000000000))
    | 17 => (orderedInterval (-3483688646 / 1000000000000) (-3483688645 / 1000000000000), orderedInterval (-26074278575 / 1000000000000) (-26074278574 / 1000000000000))
    | 18 => (orderedInterval (23031502887 / 1000000000000) (23031502888 / 1000000000000), orderedInterval (26821656261 / 1000000000000) (26821656262 / 1000000000000))
    | 19 => (orderedInterval (-37767607887 / 1000000000000) (-37767604873 / 1000000000000), orderedInterval (7073938948 / 1000000000000) (7073941962 / 1000000000000))
    | 20 => (orderedInterval (24884320707 / 1000000000000) (24884320708 / 1000000000000), orderedInterval (41658040761 / 1000000000000) (41658040762 / 1000000000000))
    | 21 => (orderedInterval (65660831369 / 1000000000000) (65660831375 / 1000000000000), orderedInterval (8375723386 / 1000000000000) (8375723392 / 1000000000000))
    | 22 => (orderedInterval (-31300477572 / 1000000000000) (-31300426338 / 1000000000000), orderedInterval (25246827083 / 1000000000000) (25246878316 / 1000000000000))
    | 23 => (orderedInterval (-33723712748 / 1000000000000) (-33723706557 / 1000000000000), orderedInterval (6783293797 / 1000000000000) (6783299988 / 1000000000000))
    | 24 => (orderedInterval (43967881062 / 1000000000000) (43967938358 / 1000000000000), orderedInterval (-29495411153 / 1000000000000) (-29495353857 / 1000000000000))
    | 25 => (orderedInterval (20953890156 / 1000000000000) (20953895455 / 1000000000000), orderedInterval (-15795110345 / 1000000000000) (-15795105045 / 1000000000000))
    | _ => (orderedInterval (6746950029 / 1000000000000) (6746950032 / 1000000000000), orderedInterval (-31386666346 / 1000000000000) (-31386666342 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14321335064 / 1000000000000) (14321343489 / 1000000000000)
      | 1 => orderedInterval (-4142748499 / 1000000000000) (-4142746139 / 1000000000000)
      | 2 => orderedInterval (655091532 / 1000000000000) (655094120 / 1000000000000)
      | 3 => orderedInterval (-2227918990 / 1000000000000) (-2227916287 / 1000000000000)
      | 4 => orderedInterval (1357417359 / 1000000000000) (1357417489 / 1000000000000)
      | 5 => orderedInterval (-1429418658 / 1000000000000) (-1429418610 / 1000000000000)
      | 6 => orderedInterval (-734802724 / 1000000000000) (-734802428 / 1000000000000)
      | 7 => orderedInterval (2082220252 / 1000000000000) (2082221949 / 1000000000000)
      | _ => orderedInterval (-2706538388 / 1000000000000) (-2706537473 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7109238100 / 1000000000000) (-7109229669 / 1000000000000)
      | 1 => orderedInterval (387238701 / 1000000000000) (387240272 / 1000000000000)
      | 2 => orderedInterval (-1415536796 / 1000000000000) (-1415531684 / 1000000000000)
      | 3 => orderedInterval (-13616173750 / 1000000000000) (-13616170096 / 1000000000000)
      | 4 => orderedInterval (4512248729 / 1000000000000) (4512248946 / 1000000000000)
      | 5 => orderedInterval (-3143697029 / 1000000000000) (-3143696960 / 1000000000000)
      | 6 => orderedInterval (-3997854076 / 1000000000000) (-3997853813 / 1000000000000)
      | 7 => orderedInterval (-1061318647 / 1000000000000) (-1061317159 / 1000000000000)
      | _ => orderedInterval (9623532162 / 1000000000000) (9623533317 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14603131365 / 1000000000000) (-14603122910 / 1000000000000)
      | 1 => orderedInterval (5505682457 / 1000000000000) (5505683695 / 1000000000000)
      | 2 => orderedInterval (-2749981390 / 1000000000000) (-2749971274 / 1000000000000)
      | 3 => orderedInterval (17675978794 / 1000000000000) (17675983892 / 1000000000000)
      | 4 => orderedInterval (-3692629796 / 1000000000000) (-3692629427 / 1000000000000)
      | 5 => orderedInterval (2454170487 / 1000000000000) (2454170590 / 1000000000000)
      | 6 => orderedInterval (2015131067 / 1000000000000) (2015131306 / 1000000000000)
      | 7 => orderedInterval (-3365055912 / 1000000000000) (-3365054570 / 1000000000000)
      | _ => orderedInterval (7775227715 / 1000000000000) (7775229567 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (7876524324 / 1000000000000) (7876532788 / 1000000000000)
      | 1 => orderedInterval (-105780707 / 1000000000000) (-105779477 / 1000000000000)
      | 2 => orderedInterval (3698525996 / 1000000000000) (3698545996 / 1000000000000)
      | 3 => orderedInterval (64276532155 / 1000000000000) (64276539580 / 1000000000000)
      | 4 => orderedInterval (-12218412900 / 1000000000000) (-12218412267 / 1000000000000)
      | 5 => orderedInterval (7542684824 / 1000000000000) (7542684983 / 1000000000000)
      | 6 => orderedInterval (4629486903 / 1000000000000) (4629487121 / 1000000000000)
      | 7 => orderedInterval (953619431 / 1000000000000) (953620667 / 1000000000000)
      | _ => orderedInterval (-19546962948 / 1000000000000) (-19546959697 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15055361972 / 1000000000000) (15055370464 / 1000000000000)
      | 1 => orderedInterval (-12427663453 / 1000000000000) (-12427661933 / 1000000000000)
      | 2 => orderedInterval (11161811414 / 1000000000000) (11161851005 / 1000000000000)
      | 3 => orderedInterval (-99665963541 / 1000000000000) (-99665952037 / 1000000000000)
      | 4 => orderedInterval (11153393562 / 1000000000000) (11153394660 / 1000000000000)
      | 5 => orderedInterval (-4480334791 / 1000000000000) (-4480334540 / 1000000000000)
      | 6 => orderedInterval (-2770827561 / 1000000000000) (-2770827359 / 1000000000000)
      | 7 => orderedInterval (3806917019 / 1000000000000) (3806918190 / 1000000000000)
      | _ => orderedInterval (-23311461634 / 1000000000000) (-23311455743 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (7174636948 / 1000000000000) (7174656110 / 1000000000000)
    | 1 => orderedInterval (-15820798806 / 1000000000000) (-15820776846 / 1000000000000)
    | 2 => orderedInterval (11015392057 / 1000000000000) (11015420869 / 1000000000000)
    | 3 => orderedInterval (57106217078 / 1000000000000) (57106259694 / 1000000000000)
    | _ => orderedInterval (-101478767013 / 1000000000000) (-101478697293 / 1000000000000)

theorem compactCertificate626_stateChecks0 :
    compactCertificate626.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (995 / 2)) (orderedInterval (33691755010 / 1000000000000) (33691776154 / 1000000000000), orderedInterval (-12054775873 / 1000000000000) (-12054754728 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (293164998632299 / 800000000000)) (orderedInterval (13310210498 / 1000000000000) (13310210613 / 1000000000000), orderedInterval (-39515910892 / 1000000000000) (-39515910777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (94803537102667 / 160000000000)) (orderedInterval (14367094825 / 1000000000000) (14367094966 / 1000000000000), orderedInterval (-29474141364 / 1000000000000) (-29474141224 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_stateChecks1 :
    compactCertificate626.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (85544815436993 / 800000000000)) (orderedInterval (60493257441 / 1000000000000) (60493257442 / 1000000000000), orderedInterval (47613977036 / 1000000000000) (47613977037 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (229785407137421 / 800000000000)) (orderedInterval (-39862729729 / 1000000000000) (-39862671540 / 1000000000000), orderedInterval (25116539057 / 1000000000000) (25116597246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (623912080005657 / 800000000000)) (orderedInterval (28569302764 / 1000000000000) (28569305240 / 1000000000000), orderedInterval (279857704 / 1000000000000) (279860181 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_stateChecks2 :
    compactCertificate626.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (459570814275041 / 800000000000)) (orderedInterval (-11015082709 / 1000000000000) (-11015082708 / 1000000000000), orderedInterval (-31404853128 / 1000000000000) (-31404853127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 313 12 (787482423393893 / 800000000000)) (orderedInterval (-24646775193 / 1000000000000) (-24646692225 / 1000000000000), orderedInterval (6279668079 / 1000000000000) (6279751047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (580055988887087 / 800000000000)) (orderedInterval (-4349178085 / 1000000000000) (-4349178084 / 1000000000000), orderedInterval (-29307345974 / 1000000000000) (-29307345973 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_stateChecks3 :
    compactCertificate626.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 354 12 (889955055044801 / 800000000000)) (orderedInterval (21376901602 / 1000000000000) (21376901667 / 1000000000000), orderedInterval (10728149273 / 1000000000000) (10728149338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (513815790596729 / 800000000000)) (orderedInterval (25997761946 / 1000000000000) (25997795610 / 1000000000000), orderedInterval (-17777465137 / 1000000000000) (-17777431474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 363 12 (911775137019661 / 800000000000)) (orderedInterval (-2502335920 / 1000000000000) (-2502335919 / 1000000000000), orderedInterval (-23500274238 / 1000000000000) (-23500274237 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_stateChecks4 :
    compactCertificate626.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 339 12 (851898605363809 / 800000000000)) (orderedInterval (-14964611563 / 1000000000000) (-14964611562 / 1000000000000), orderedInterval (-19329379836 / 1000000000000) (-19329379835 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (607955042197297 / 800000000000)) (orderedInterval (12943010450 / 1000000000000) (12943010451 / 1000000000000), orderedInterval (25879669351 / 1000000000000) (25879669352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (689356221412263 / 800000000000)) (orderedInterval (27006436295 / 1000000000000) (27006450074 / 1000000000000), orderedInterval (-3089939212 / 1000000000000) (-3089925434 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_stateChecks5 :
    compactCertificate626.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (574713348414647 / 800000000000)) (orderedInterval (7301643315 / 1000000000000) (7301643317 / 1000000000000), orderedInterval (-28864392915 / 1000000000000) (-28864392912 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (507776672631587 / 800000000000)) (orderedInterval (24892925581 / 1000000000000) (24892925582 / 1000000000000), orderedInterval (19559306397 / 1000000000000) (19559306398 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (147173471275113 / 160000000000)) (orderedInterval (-3483688646 / 1000000000000) (-3483688645 / 1000000000000), orderedInterval (-26074278575 / 1000000000000) (-26074278574 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_stateChecks6 :
    compactCertificate626.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (407089566862411 / 800000000000)) (orderedInterval (23031502887 / 1000000000000) (23031502888 / 1000000000000), orderedInterval (26821656261 / 1000000000000) (26821656262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (345094334222771 / 800000000000)) (orderedInterval (-37767607887 / 1000000000000) (-37767604873 / 1000000000000), orderedInterval (7073938948 / 1000000000000) (7073941962 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (215944011112913 / 800000000000)) (orderedInterval (24884320707 / 1000000000000) (24884320708 / 1000000000000), orderedInterval (41658040761 / 1000000000000) (41658040762 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_stateChecks7 :
    compactCertificate626.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (116135407373871 / 800000000000)) (orderedInterval (65660831369 / 1000000000000) (65660831375 / 1000000000000), orderedInterval (8375723386 / 1000000000000) (8375723392 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (315330222574613 / 800000000000)) (orderedInterval (-31300477572 / 1000000000000) (-31300426338 / 1000000000000), orderedInterval (25246827083 / 1000000000000) (25246878316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (430556460515701 / 800000000000)) (orderedInterval (-33723712748 / 1000000000000) (-33723706557 / 1000000000000), orderedInterval (6783293797 / 1000000000000) (6783299988 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_stateChecks8 :
    compactCertificate626.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (182055988887087 / 800000000000)) (orderedInterval (43967881062 / 1000000000000) (43967938358 / 1000000000000), orderedInterval (-29495411153 / 1000000000000) (-29495353857 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 295 12 (740047487379727 / 800000000000)) (orderedInterval (20953890156 / 1000000000000) (20953895455 / 1000000000000), orderedInterval (-15795110345 / 1000000000000) (-15795105045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (494317424761793 / 800000000000)) (orderedInterval (6746950029 / 1000000000000) (6746950032 / 1000000000000), orderedInterval (-31386666346 / 1000000000000) (-31386666342 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_states : ∀ j,
    BesselStateValid (compactCertificate626.point j) (compactCertificate626.state j) :=
  compactCertificate626.statesValid_of_checks3 compactCertificate626_stateChecks0
    compactCertificate626_stateChecks1 compactCertificate626_stateChecks2
    compactCertificate626_stateChecks3 compactCertificate626_stateChecks4
    compactCertificate626_stateChecks5 compactCertificate626_stateChecks6
    compactCertificate626_stateChecks7 compactCertificate626_stateChecks8

theorem compactCertificate626_chunkChecks0_0 :
    compactCertificate626.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (995 / 2) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33691755010 / 1000000000000) (33691776154 / 1000000000000), orderedInterval (-12054775873 / 1000000000000) (-12054754728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (293164998632299 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13310210498 / 1000000000000) (13310210613 / 1000000000000), orderedInterval (-39515910892 / 1000000000000) (-39515910777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (94803537102667 / 160000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14367094825 / 1000000000000) (14367094966 / 1000000000000), orderedInterval (-29474141364 / 1000000000000) (-29474141224 / 1000000000000)))) (orderedInterval (14321335064 / 1000000000000) (14321343489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (85544815436993 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60493257441 / 1000000000000) (60493257442 / 1000000000000), orderedInterval (47613977036 / 1000000000000) (47613977037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (229785407137421 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39862729729 / 1000000000000) (-39862671540 / 1000000000000), orderedInterval (25116539057 / 1000000000000) (25116597246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (623912080005657 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28569302764 / 1000000000000) (28569305240 / 1000000000000), orderedInterval (279857704 / 1000000000000) (279860181 / 1000000000000)))) (orderedInterval (-4142748499 / 1000000000000) (-4142746139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (459570814275041 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-11015082709 / 1000000000000) (-11015082708 / 1000000000000), orderedInterval (-31404853128 / 1000000000000) (-31404853127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (787482423393893 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24646775193 / 1000000000000) (-24646692225 / 1000000000000), orderedInterval (6279668079 / 1000000000000) (6279751047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (580055988887087 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4349178085 / 1000000000000) (-4349178084 / 1000000000000), orderedInterval (-29307345974 / 1000000000000) (-29307345973 / 1000000000000)))) (orderedInterval (655091532 / 1000000000000) (655094120 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks0_1 :
    compactCertificate626.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (889955055044801 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21376901602 / 1000000000000) (21376901667 / 1000000000000), orderedInterval (10728149273 / 1000000000000) (10728149338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (513815790596729 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25997761946 / 1000000000000) (25997795610 / 1000000000000), orderedInterval (-17777465137 / 1000000000000) (-17777431474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (911775137019661 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2502335920 / 1000000000000) (-2502335919 / 1000000000000), orderedInterval (-23500274238 / 1000000000000) (-23500274237 / 1000000000000)))) (orderedInterval (-2227918990 / 1000000000000) (-2227916287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (851898605363809 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14964611563 / 1000000000000) (-14964611562 / 1000000000000), orderedInterval (-19329379836 / 1000000000000) (-19329379835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (607955042197297 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12943010450 / 1000000000000) (12943010451 / 1000000000000), orderedInterval (25879669351 / 1000000000000) (25879669352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (689356221412263 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27006436295 / 1000000000000) (27006450074 / 1000000000000), orderedInterval (-3089939212 / 1000000000000) (-3089925434 / 1000000000000)))) (orderedInterval (1357417359 / 1000000000000) (1357417489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (574713348414647 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7301643315 / 1000000000000) (7301643317 / 1000000000000), orderedInterval (-28864392915 / 1000000000000) (-28864392912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (507776672631587 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24892925581 / 1000000000000) (24892925582 / 1000000000000), orderedInterval (19559306397 / 1000000000000) (19559306398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (147173471275113 / 160000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3483688646 / 1000000000000) (-3483688645 / 1000000000000), orderedInterval (-26074278575 / 1000000000000) (-26074278574 / 1000000000000)))) (orderedInterval (-1429418658 / 1000000000000) (-1429418610 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks0_2 :
    compactCertificate626.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (407089566862411 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23031502887 / 1000000000000) (23031502888 / 1000000000000), orderedInterval (26821656261 / 1000000000000) (26821656262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (345094334222771 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37767607887 / 1000000000000) (-37767604873 / 1000000000000), orderedInterval (7073938948 / 1000000000000) (7073941962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (215944011112913 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24884320707 / 1000000000000) (24884320708 / 1000000000000), orderedInterval (41658040761 / 1000000000000) (41658040762 / 1000000000000)))) (orderedInterval (-734802724 / 1000000000000) (-734802428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (116135407373871 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65660831369 / 1000000000000) (65660831375 / 1000000000000), orderedInterval (8375723386 / 1000000000000) (8375723392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (315330222574613 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31300477572 / 1000000000000) (-31300426338 / 1000000000000), orderedInterval (25246827083 / 1000000000000) (25246878316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (430556460515701 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33723712748 / 1000000000000) (-33723706557 / 1000000000000), orderedInterval (6783293797 / 1000000000000) (6783299988 / 1000000000000)))) (orderedInterval (2082220252 / 1000000000000) (2082221949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (182055988887087 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43967881062 / 1000000000000) (43967938358 / 1000000000000), orderedInterval (-29495411153 / 1000000000000) (-29495353857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (740047487379727 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20953890156 / 1000000000000) (20953895455 / 1000000000000), orderedInterval (-15795110345 / 1000000000000) (-15795105045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (494317424761793 / 800000000000) 0 (IntervalRat.scale (995 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6746950029 / 1000000000000) (6746950032 / 1000000000000), orderedInterval (-31386666346 / 1000000000000) (-31386666342 / 1000000000000)))) (orderedInterval (-2706538388 / 1000000000000) (-2706537473 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks0 :
    compactCertificate626.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate626.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate626_chunkChecks0_0
    compactCertificate626_chunkChecks0_1 compactCertificate626_chunkChecks0_2

theorem compactCertificate626_chunkChecks1_0 :
    compactCertificate626.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (995 / 2) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33691755010 / 1000000000000) (33691776154 / 1000000000000), orderedInterval (-12054775873 / 1000000000000) (-12054754728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (293164998632299 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13310210498 / 1000000000000) (13310210613 / 1000000000000), orderedInterval (-39515910892 / 1000000000000) (-39515910777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (94803537102667 / 160000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14367094825 / 1000000000000) (14367094966 / 1000000000000), orderedInterval (-29474141364 / 1000000000000) (-29474141224 / 1000000000000)))) (orderedInterval (-7109238100 / 1000000000000) (-7109229669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (85544815436993 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60493257441 / 1000000000000) (60493257442 / 1000000000000), orderedInterval (47613977036 / 1000000000000) (47613977037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (229785407137421 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39862729729 / 1000000000000) (-39862671540 / 1000000000000), orderedInterval (25116539057 / 1000000000000) (25116597246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (623912080005657 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28569302764 / 1000000000000) (28569305240 / 1000000000000), orderedInterval (279857704 / 1000000000000) (279860181 / 1000000000000)))) (orderedInterval (387238701 / 1000000000000) (387240272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (459570814275041 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-11015082709 / 1000000000000) (-11015082708 / 1000000000000), orderedInterval (-31404853128 / 1000000000000) (-31404853127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (787482423393893 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24646775193 / 1000000000000) (-24646692225 / 1000000000000), orderedInterval (6279668079 / 1000000000000) (6279751047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (580055988887087 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4349178085 / 1000000000000) (-4349178084 / 1000000000000), orderedInterval (-29307345974 / 1000000000000) (-29307345973 / 1000000000000)))) (orderedInterval (-1415536796 / 1000000000000) (-1415531684 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks1_1 :
    compactCertificate626.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (889955055044801 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21376901602 / 1000000000000) (21376901667 / 1000000000000), orderedInterval (10728149273 / 1000000000000) (10728149338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (513815790596729 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25997761946 / 1000000000000) (25997795610 / 1000000000000), orderedInterval (-17777465137 / 1000000000000) (-17777431474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (911775137019661 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2502335920 / 1000000000000) (-2502335919 / 1000000000000), orderedInterval (-23500274238 / 1000000000000) (-23500274237 / 1000000000000)))) (orderedInterval (-13616173750 / 1000000000000) (-13616170096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (851898605363809 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14964611563 / 1000000000000) (-14964611562 / 1000000000000), orderedInterval (-19329379836 / 1000000000000) (-19329379835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (607955042197297 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12943010450 / 1000000000000) (12943010451 / 1000000000000), orderedInterval (25879669351 / 1000000000000) (25879669352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (689356221412263 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27006436295 / 1000000000000) (27006450074 / 1000000000000), orderedInterval (-3089939212 / 1000000000000) (-3089925434 / 1000000000000)))) (orderedInterval (4512248729 / 1000000000000) (4512248946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (574713348414647 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7301643315 / 1000000000000) (7301643317 / 1000000000000), orderedInterval (-28864392915 / 1000000000000) (-28864392912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (507776672631587 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24892925581 / 1000000000000) (24892925582 / 1000000000000), orderedInterval (19559306397 / 1000000000000) (19559306398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (147173471275113 / 160000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3483688646 / 1000000000000) (-3483688645 / 1000000000000), orderedInterval (-26074278575 / 1000000000000) (-26074278574 / 1000000000000)))) (orderedInterval (-3143697029 / 1000000000000) (-3143696960 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks1_2 :
    compactCertificate626.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (407089566862411 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23031502887 / 1000000000000) (23031502888 / 1000000000000), orderedInterval (26821656261 / 1000000000000) (26821656262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (345094334222771 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37767607887 / 1000000000000) (-37767604873 / 1000000000000), orderedInterval (7073938948 / 1000000000000) (7073941962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (215944011112913 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24884320707 / 1000000000000) (24884320708 / 1000000000000), orderedInterval (41658040761 / 1000000000000) (41658040762 / 1000000000000)))) (orderedInterval (-3997854076 / 1000000000000) (-3997853813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (116135407373871 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65660831369 / 1000000000000) (65660831375 / 1000000000000), orderedInterval (8375723386 / 1000000000000) (8375723392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (315330222574613 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31300477572 / 1000000000000) (-31300426338 / 1000000000000), orderedInterval (25246827083 / 1000000000000) (25246878316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (430556460515701 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33723712748 / 1000000000000) (-33723706557 / 1000000000000), orderedInterval (6783293797 / 1000000000000) (6783299988 / 1000000000000)))) (orderedInterval (-1061318647 / 1000000000000) (-1061317159 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (182055988887087 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43967881062 / 1000000000000) (43967938358 / 1000000000000), orderedInterval (-29495411153 / 1000000000000) (-29495353857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (740047487379727 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20953890156 / 1000000000000) (20953895455 / 1000000000000), orderedInterval (-15795110345 / 1000000000000) (-15795105045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (494317424761793 / 800000000000) 1 (IntervalRat.scale (995 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6746950029 / 1000000000000) (6746950032 / 1000000000000), orderedInterval (-31386666346 / 1000000000000) (-31386666342 / 1000000000000)))) (orderedInterval (9623532162 / 1000000000000) (9623533317 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks1 :
    compactCertificate626.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate626.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate626_chunkChecks1_0
    compactCertificate626_chunkChecks1_1 compactCertificate626_chunkChecks1_2

theorem compactCertificate626_chunkChecks2_0 :
    compactCertificate626.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (995 / 2) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33691755010 / 1000000000000) (33691776154 / 1000000000000), orderedInterval (-12054775873 / 1000000000000) (-12054754728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (293164998632299 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13310210498 / 1000000000000) (13310210613 / 1000000000000), orderedInterval (-39515910892 / 1000000000000) (-39515910777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (94803537102667 / 160000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14367094825 / 1000000000000) (14367094966 / 1000000000000), orderedInterval (-29474141364 / 1000000000000) (-29474141224 / 1000000000000)))) (orderedInterval (-14603131365 / 1000000000000) (-14603122910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (85544815436993 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60493257441 / 1000000000000) (60493257442 / 1000000000000), orderedInterval (47613977036 / 1000000000000) (47613977037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (229785407137421 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39862729729 / 1000000000000) (-39862671540 / 1000000000000), orderedInterval (25116539057 / 1000000000000) (25116597246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (623912080005657 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28569302764 / 1000000000000) (28569305240 / 1000000000000), orderedInterval (279857704 / 1000000000000) (279860181 / 1000000000000)))) (orderedInterval (5505682457 / 1000000000000) (5505683695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (459570814275041 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-11015082709 / 1000000000000) (-11015082708 / 1000000000000), orderedInterval (-31404853128 / 1000000000000) (-31404853127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (787482423393893 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24646775193 / 1000000000000) (-24646692225 / 1000000000000), orderedInterval (6279668079 / 1000000000000) (6279751047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (580055988887087 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4349178085 / 1000000000000) (-4349178084 / 1000000000000), orderedInterval (-29307345974 / 1000000000000) (-29307345973 / 1000000000000)))) (orderedInterval (-2749981390 / 1000000000000) (-2749971274 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks2_1 :
    compactCertificate626.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (889955055044801 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21376901602 / 1000000000000) (21376901667 / 1000000000000), orderedInterval (10728149273 / 1000000000000) (10728149338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (513815790596729 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25997761946 / 1000000000000) (25997795610 / 1000000000000), orderedInterval (-17777465137 / 1000000000000) (-17777431474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (911775137019661 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2502335920 / 1000000000000) (-2502335919 / 1000000000000), orderedInterval (-23500274238 / 1000000000000) (-23500274237 / 1000000000000)))) (orderedInterval (17675978794 / 1000000000000) (17675983892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (851898605363809 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14964611563 / 1000000000000) (-14964611562 / 1000000000000), orderedInterval (-19329379836 / 1000000000000) (-19329379835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (607955042197297 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12943010450 / 1000000000000) (12943010451 / 1000000000000), orderedInterval (25879669351 / 1000000000000) (25879669352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (689356221412263 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27006436295 / 1000000000000) (27006450074 / 1000000000000), orderedInterval (-3089939212 / 1000000000000) (-3089925434 / 1000000000000)))) (orderedInterval (-3692629796 / 1000000000000) (-3692629427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (574713348414647 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7301643315 / 1000000000000) (7301643317 / 1000000000000), orderedInterval (-28864392915 / 1000000000000) (-28864392912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (507776672631587 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24892925581 / 1000000000000) (24892925582 / 1000000000000), orderedInterval (19559306397 / 1000000000000) (19559306398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (147173471275113 / 160000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3483688646 / 1000000000000) (-3483688645 / 1000000000000), orderedInterval (-26074278575 / 1000000000000) (-26074278574 / 1000000000000)))) (orderedInterval (2454170487 / 1000000000000) (2454170590 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks2_2 :
    compactCertificate626.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (407089566862411 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23031502887 / 1000000000000) (23031502888 / 1000000000000), orderedInterval (26821656261 / 1000000000000) (26821656262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (345094334222771 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37767607887 / 1000000000000) (-37767604873 / 1000000000000), orderedInterval (7073938948 / 1000000000000) (7073941962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (215944011112913 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24884320707 / 1000000000000) (24884320708 / 1000000000000), orderedInterval (41658040761 / 1000000000000) (41658040762 / 1000000000000)))) (orderedInterval (2015131067 / 1000000000000) (2015131306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (116135407373871 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65660831369 / 1000000000000) (65660831375 / 1000000000000), orderedInterval (8375723386 / 1000000000000) (8375723392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (315330222574613 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31300477572 / 1000000000000) (-31300426338 / 1000000000000), orderedInterval (25246827083 / 1000000000000) (25246878316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (430556460515701 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33723712748 / 1000000000000) (-33723706557 / 1000000000000), orderedInterval (6783293797 / 1000000000000) (6783299988 / 1000000000000)))) (orderedInterval (-3365055912 / 1000000000000) (-3365054570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (182055988887087 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43967881062 / 1000000000000) (43967938358 / 1000000000000), orderedInterval (-29495411153 / 1000000000000) (-29495353857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (740047487379727 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20953890156 / 1000000000000) (20953895455 / 1000000000000), orderedInterval (-15795110345 / 1000000000000) (-15795105045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (494317424761793 / 800000000000) 2 (IntervalRat.scale (995 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6746950029 / 1000000000000) (6746950032 / 1000000000000), orderedInterval (-31386666346 / 1000000000000) (-31386666342 / 1000000000000)))) (orderedInterval (7775227715 / 1000000000000) (7775229567 / 1000000000000))) = true
  rfl'

theorem compactCertificate626_chunkChecks2 :
    compactCertificate626.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate626.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate626_chunkChecks2_0
    compactCertificate626_chunkChecks2_1 compactCertificate626_chunkChecks2_2

theorem compactCertificate626_chunkChecks3_0 :
    compactCertificate626.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (995 / 2) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33691755010 / 1000000000000) (33691776154 / 1000000000000), orderedInterval (-12054775873 / 1000000000000) (-12054754728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (293164998632299 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13310210498 / 1000000000000) (13310210613 / 1000000000000), orderedInterval (-39515910892 / 1000000000000) (-39515910777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (94803537102667 / 160000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14367094825 / 1000000000000) (14367094966 / 1000000000000), orderedInterval (-29474141364 / 1000000000000) (-29474141224 / 1000000000000)))) (orderedInterval (7876524324 / 1000000000000) (7876532788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (85544815436993 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60493257441 / 1000000000000) (60493257442 / 1000000000000), orderedInterval (47613977036 / 1000000000000) (47613977037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (229785407137421 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39862729729 / 1000000000000) (-39862671540 / 1000000000000), orderedInterval (25116539057 / 1000000000000) (25116597246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (623912080005657 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28569302764 / 1000000000000) (28569305240 / 1000000000000), orderedInterval (279857704 / 1000000000000) (279860181 / 1000000000000)))) (orderedInterval (-105780707 / 1000000000000) (-105779477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (459570814275041 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-11015082709 / 1000000000000) (-11015082708 / 1000000000000), orderedInterval (-31404853128 / 1000000000000) (-31404853127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (787482423393893 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24646775193 / 1000000000000) (-24646692225 / 1000000000000), orderedInterval (6279668079 / 1000000000000) (6279751047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (580055988887087 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4349178085 / 1000000000000) (-4349178084 / 1000000000000), orderedInterval (-29307345974 / 1000000000000) (-29307345973 / 1000000000000)))) (orderedInterval (3698525996 / 1000000000000) (3698545996 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate626_chunkChecks3_1 :
    compactCertificate626.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (889955055044801 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21376901602 / 1000000000000) (21376901667 / 1000000000000), orderedInterval (10728149273 / 1000000000000) (10728149338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (513815790596729 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25997761946 / 1000000000000) (25997795610 / 1000000000000), orderedInterval (-17777465137 / 1000000000000) (-17777431474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (911775137019661 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2502335920 / 1000000000000) (-2502335919 / 1000000000000), orderedInterval (-23500274238 / 1000000000000) (-23500274237 / 1000000000000)))) (orderedInterval (64276532155 / 1000000000000) (64276539580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (851898605363809 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14964611563 / 1000000000000) (-14964611562 / 1000000000000), orderedInterval (-19329379836 / 1000000000000) (-19329379835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (607955042197297 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12943010450 / 1000000000000) (12943010451 / 1000000000000), orderedInterval (25879669351 / 1000000000000) (25879669352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (689356221412263 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27006436295 / 1000000000000) (27006450074 / 1000000000000), orderedInterval (-3089939212 / 1000000000000) (-3089925434 / 1000000000000)))) (orderedInterval (-12218412900 / 1000000000000) (-12218412267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (574713348414647 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7301643315 / 1000000000000) (7301643317 / 1000000000000), orderedInterval (-28864392915 / 1000000000000) (-28864392912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (507776672631587 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24892925581 / 1000000000000) (24892925582 / 1000000000000), orderedInterval (19559306397 / 1000000000000) (19559306398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (147173471275113 / 160000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3483688646 / 1000000000000) (-3483688645 / 1000000000000), orderedInterval (-26074278575 / 1000000000000) (-26074278574 / 1000000000000)))) (orderedInterval (7542684824 / 1000000000000) (7542684983 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate626_chunkChecks3_2 :
    compactCertificate626.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (407089566862411 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23031502887 / 1000000000000) (23031502888 / 1000000000000), orderedInterval (26821656261 / 1000000000000) (26821656262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (345094334222771 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37767607887 / 1000000000000) (-37767604873 / 1000000000000), orderedInterval (7073938948 / 1000000000000) (7073941962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (215944011112913 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24884320707 / 1000000000000) (24884320708 / 1000000000000), orderedInterval (41658040761 / 1000000000000) (41658040762 / 1000000000000)))) (orderedInterval (4629486903 / 1000000000000) (4629487121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (116135407373871 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65660831369 / 1000000000000) (65660831375 / 1000000000000), orderedInterval (8375723386 / 1000000000000) (8375723392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (315330222574613 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31300477572 / 1000000000000) (-31300426338 / 1000000000000), orderedInterval (25246827083 / 1000000000000) (25246878316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (430556460515701 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33723712748 / 1000000000000) (-33723706557 / 1000000000000), orderedInterval (6783293797 / 1000000000000) (6783299988 / 1000000000000)))) (orderedInterval (953619431 / 1000000000000) (953620667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (182055988887087 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43967881062 / 1000000000000) (43967938358 / 1000000000000), orderedInterval (-29495411153 / 1000000000000) (-29495353857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (740047487379727 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20953890156 / 1000000000000) (20953895455 / 1000000000000), orderedInterval (-15795110345 / 1000000000000) (-15795105045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (494317424761793 / 800000000000) 3 (IntervalRat.scale (995 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6746950029 / 1000000000000) (6746950032 / 1000000000000), orderedInterval (-31386666346 / 1000000000000) (-31386666342 / 1000000000000)))) (orderedInterval (-19546962948 / 1000000000000) (-19546959697 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate626_chunkChecks3 :
    compactCertificate626.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate626.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate626_chunkChecks3_0
    compactCertificate626_chunkChecks3_1 compactCertificate626_chunkChecks3_2

theorem compactCertificate626_chunkChecks4_0 :
    compactCertificate626.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (995 / 2) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33691755010 / 1000000000000) (33691776154 / 1000000000000), orderedInterval (-12054775873 / 1000000000000) (-12054754728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (293164998632299 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13310210498 / 1000000000000) (13310210613 / 1000000000000), orderedInterval (-39515910892 / 1000000000000) (-39515910777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (94803537102667 / 160000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14367094825 / 1000000000000) (14367094966 / 1000000000000), orderedInterval (-29474141364 / 1000000000000) (-29474141224 / 1000000000000)))) (orderedInterval (15055361972 / 1000000000000) (15055370464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (85544815436993 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60493257441 / 1000000000000) (60493257442 / 1000000000000), orderedInterval (47613977036 / 1000000000000) (47613977037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (229785407137421 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39862729729 / 1000000000000) (-39862671540 / 1000000000000), orderedInterval (25116539057 / 1000000000000) (25116597246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (623912080005657 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28569302764 / 1000000000000) (28569305240 / 1000000000000), orderedInterval (279857704 / 1000000000000) (279860181 / 1000000000000)))) (orderedInterval (-12427663453 / 1000000000000) (-12427661933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (459570814275041 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-11015082709 / 1000000000000) (-11015082708 / 1000000000000), orderedInterval (-31404853128 / 1000000000000) (-31404853127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (787482423393893 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24646775193 / 1000000000000) (-24646692225 / 1000000000000), orderedInterval (6279668079 / 1000000000000) (6279751047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (580055988887087 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4349178085 / 1000000000000) (-4349178084 / 1000000000000), orderedInterval (-29307345974 / 1000000000000) (-29307345973 / 1000000000000)))) (orderedInterval (11161811414 / 1000000000000) (11161851005 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate626_chunkChecks4_1 :
    compactCertificate626.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (889955055044801 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21376901602 / 1000000000000) (21376901667 / 1000000000000), orderedInterval (10728149273 / 1000000000000) (10728149338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (513815790596729 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25997761946 / 1000000000000) (25997795610 / 1000000000000), orderedInterval (-17777465137 / 1000000000000) (-17777431474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (911775137019661 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2502335920 / 1000000000000) (-2502335919 / 1000000000000), orderedInterval (-23500274238 / 1000000000000) (-23500274237 / 1000000000000)))) (orderedInterval (-99665963541 / 1000000000000) (-99665952037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (851898605363809 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14964611563 / 1000000000000) (-14964611562 / 1000000000000), orderedInterval (-19329379836 / 1000000000000) (-19329379835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (607955042197297 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12943010450 / 1000000000000) (12943010451 / 1000000000000), orderedInterval (25879669351 / 1000000000000) (25879669352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (689356221412263 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27006436295 / 1000000000000) (27006450074 / 1000000000000), orderedInterval (-3089939212 / 1000000000000) (-3089925434 / 1000000000000)))) (orderedInterval (11153393562 / 1000000000000) (11153394660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (574713348414647 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (7301643315 / 1000000000000) (7301643317 / 1000000000000), orderedInterval (-28864392915 / 1000000000000) (-28864392912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (507776672631587 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (24892925581 / 1000000000000) (24892925582 / 1000000000000), orderedInterval (19559306397 / 1000000000000) (19559306398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (147173471275113 / 160000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3483688646 / 1000000000000) (-3483688645 / 1000000000000), orderedInterval (-26074278575 / 1000000000000) (-26074278574 / 1000000000000)))) (orderedInterval (-4480334791 / 1000000000000) (-4480334540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate626_chunkChecks4_2 :
    compactCertificate626.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (407089566862411 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23031502887 / 1000000000000) (23031502888 / 1000000000000), orderedInterval (26821656261 / 1000000000000) (26821656262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (345094334222771 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37767607887 / 1000000000000) (-37767604873 / 1000000000000), orderedInterval (7073938948 / 1000000000000) (7073941962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (215944011112913 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24884320707 / 1000000000000) (24884320708 / 1000000000000), orderedInterval (41658040761 / 1000000000000) (41658040762 / 1000000000000)))) (orderedInterval (-2770827561 / 1000000000000) (-2770827359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (116135407373871 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65660831369 / 1000000000000) (65660831375 / 1000000000000), orderedInterval (8375723386 / 1000000000000) (8375723392 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (315330222574613 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31300477572 / 1000000000000) (-31300426338 / 1000000000000), orderedInterval (25246827083 / 1000000000000) (25246878316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (430556460515701 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33723712748 / 1000000000000) (-33723706557 / 1000000000000), orderedInterval (6783293797 / 1000000000000) (6783299988 / 1000000000000)))) (orderedInterval (3806917019 / 1000000000000) (3806918190 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (182055988887087 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43967881062 / 1000000000000) (43967938358 / 1000000000000), orderedInterval (-29495411153 / 1000000000000) (-29495353857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (740047487379727 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20953890156 / 1000000000000) (20953895455 / 1000000000000), orderedInterval (-15795110345 / 1000000000000) (-15795105045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (494317424761793 / 800000000000) 4 (IntervalRat.scale (995 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6746950029 / 1000000000000) (6746950032 / 1000000000000), orderedInterval (-31386666346 / 1000000000000) (-31386666342 / 1000000000000)))) (orderedInterval (-23311461634 / 1000000000000) (-23311455743 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate626_chunkChecks4 :
    compactCertificate626.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate626.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate626_chunkChecks4_0
    compactCertificate626_chunkChecks4_1 compactCertificate626_chunkChecks4_2

theorem compactCertificate626_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate626.chunkCheck r b = true :=
  compactCertificate626.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate626_chunkChecks0
    · exact compactCertificate626_chunkChecks1
    · exact compactCertificate626_chunkChecks2
    · exact compactCertificate626_chunkChecks3
    · exact compactCertificate626_chunkChecks4)

theorem compactCertificate626_coefficient0 :
    compactCertificate626.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate626_coefficient1 :
    compactCertificate626.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate626_coefficient2 :
    compactCertificate626.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate626_coefficient3 :
    compactCertificate626.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate626_coefficient4 :
    compactCertificate626.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate626_coefficients : ∀ r : Fin 5,
    compactCertificate626.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate626_coefficient0
  · exact compactCertificate626_coefficient1
  · exact compactCertificate626_coefficient2
  · exact compactCertificate626_coefficient3
  · exact compactCertificate626_coefficient4

theorem compactCertificate626_lower : (1 : ℚ) ≤ compactCertificate626.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate626, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate626_proves {t : ℝ} (ht : t ∈ compactCertificate626.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate626.proves compactCertificate626_states compactCertificate626_chunks
    compactCertificate626_coefficients compactCertificate626_lower ht

end Erdos232
