/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate524 : CompactCertificate where
  left := 395
  right := 396
  center := 791 / 2
  grid := fun i =>
    match i.val with
    | 0 => 126
    | 1 => 93
    | 2 => 150
    | 3 => 27
    | 4 => 73
    | 5 => 197
    | 6 => 145
    | 7 => 249
    | 8 => 184
    | 9 => 282
    | 10 => 163
    | 11 => 289
    | 12 => 270
    | 13 => 192
    | 14 => 218
    | 15 => 182
    | 16 => 161
    | 17 => 233
    | 18 => 129
    | 19 => 109
    | 20 => 68
    | 21 => 37
    | 22 => 100
    | 23 => 136
    | 24 => 58
    | 25 => 234
    | _ => 156
  point := fun i =>
    match i.val with
    | 0 => 791 / 2
    | 1 => 1165294039789691 / 4000000000000
    | 2 => 376832149991003 / 800000000000
    | 3 => 340029894525937 / 4000000000000
    | 4 => 913368125857789 / 4000000000000
    | 5 => 2479972137107913 / 4000000000000
    | 6 => 1826736251716369 / 4000000000000
    | 7 => 3130143703038037 / 4000000000000
    | 8 => 2305649684470783 / 4000000000000
    | 9 => 3537459540404209 / 4000000000000
    | 10 => 2042353217899561 / 4000000000000
    | 11 => 3624191625037949 / 4000000000000
    | 12 => 3386189933883281 / 4000000000000
    | 13 => 2416544916472673 / 4000000000000
    | 14 => 2740104377573367 / 4000000000000
    | 15 => 2284413359778823 / 4000000000000
    | 16 => 2018348482671283 / 4000000000000
    | 17 => 584996059189017 / 800000000000
    | 18 => 1618129886372699 / 4000000000000
    | 19 => 1371706624975939 / 4000000000000
    | 20 => 858350315529217 / 4000000000000
    | 21 => 461623654435839 / 4000000000000
    | 22 => 1253398020384517 / 4000000000000
    | 23 => 1711407840542309 / 4000000000000
    | 24 => 723649684470783 / 4000000000000
    | 25 => 2941595791544543 / 4000000000000
    | _ => 1964849663249137 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (17248747536 / 1000000000000) (17248747537 / 1000000000000), orderedInterval (36201661361 / 1000000000000) (36201661362 / 1000000000000))
    | 1 => (orderedInterval (2786222083 / 1000000000000) (2786222086 / 1000000000000), orderedInterval (-46668553523 / 1000000000000) (-46668553519 / 1000000000000))
    | 2 => (orderedInterval (20344077455 / 1000000000000) (20344077456 / 1000000000000), orderedInterval (30599277590 / 1000000000000) (30599277591 / 1000000000000))
    | 3 => (orderedInterval (-71305734004 / 1000000000000) (-71305734003 / 1000000000000), orderedInterval (-48615612348 / 1000000000000) (-48615612347 / 1000000000000))
    | 4 => (orderedInterval (10975062017 / 1000000000000) (10975062077 / 1000000000000), orderedInterval (-51672494729 / 1000000000000) (-51672494668 / 1000000000000))
    | 5 => (orderedInterval (-30480384403 / 1000000000000) (-30480355645 / 1000000000000), orderedInterval (9912153249 / 1000000000000) (9912182007 / 1000000000000))
    | 6 => (orderedInterval (-34843953399 / 1000000000000) (-34843931431 / 1000000000000), orderedInterval (13450960803 / 1000000000000) (13450982772 / 1000000000000))
    | 7 => (orderedInterval (-24945563232 / 1000000000000) (-24945563229 / 1000000000000), orderedInterval (-13813487341 / 1000000000000) (-13813487338 / 1000000000000))
    | 8 => (orderedInterval (-25086600752 / 1000000000000) (-25086585228 / 1000000000000), orderedInterval (21818877799 / 1000000000000) (21818893322 / 1000000000000))
    | 9 => (orderedInterval (-18849801055 / 1000000000000) (-18849799730 / 1000000000000), orderedInterval (19103744479 / 1000000000000) (19103745804 / 1000000000000))
    | 10 => (orderedInterval (22913200416 / 1000000000000) (22913205240 / 1000000000000), orderedInterval (-26889167360 / 1000000000000) (-26889162536 / 1000000000000))
    | 11 => (orderedInterval (23466492459 / 1000000000000) (23466520969 / 1000000000000), orderedInterval (-12340034394 / 1000000000000) (-12340005884 / 1000000000000))
    | 12 => (orderedInterval (-21434744082 / 1000000000000) (-21434738084 / 1000000000000), orderedInterval (17117358734 / 1000000000000) (17117364732 / 1000000000000))
    | 13 => (orderedInterval (32021790101 / 1000000000000) (32021796334 / 1000000000000), orderedInterval (-5353135042 / 1000000000000) (-5353128809 / 1000000000000))
    | 14 => (orderedInterval (24692139695 / 1000000000000) (24692139696 / 1000000000000), orderedInterval (17860307368 / 1000000000000) (17860307369 / 1000000000000))
    | 15 => (orderedInterval (3952335338 / 1000000000000) (3952335339 / 1000000000000), orderedInterval (33149194388 / 1000000000000) (33149194389 / 1000000000000))
    | 16 => (orderedInterval (14617960772 / 1000000000000) (14617960944 / 1000000000000), orderedInterval (-32387009880 / 1000000000000) (-32387009707 / 1000000000000))
    | 17 => (orderedInterval (-1156715182 / 1000000000000) (-1156715181 / 1000000000000), orderedInterval (-29482411403 / 1000000000000) (-29482411402 / 1000000000000))
    | 18 => (orderedInterval (-2066211454 / 1000000000000) (-2066211453 / 1000000000000), orderedInterval (-39613722172 / 1000000000000) (-39613722171 / 1000000000000))
    | 19 => (orderedInterval (-41253697176 / 1000000000000) (-41253697174 / 1000000000000), orderedInterval (-12372151659 / 1000000000000) (-12372151656 / 1000000000000))
    | 20 => (orderedInterval (53651625201 / 1000000000000) (53651625953 / 1000000000000), orderedInterval (-9516951681 / 1000000000000) (-9516950928 / 1000000000000))
    | 21 => (orderedInterval (3615570451 / 1000000000000) (3615570464 / 1000000000000), orderedInterval (-74200112115 / 1000000000000) (-74200112103 / 1000000000000))
    | 22 => (orderedInterval (-1115961743 / 1000000000000) (-1115961741 / 1000000000000), orderedInterval (45061935880 / 1000000000000) (45061935882 / 1000000000000))
    | 23 => (orderedInterval (37877284317 / 1000000000000) (37877284339 / 1000000000000), orderedInterval (7253298497 / 1000000000000) (7253298519 / 1000000000000))
    | 24 => (orderedInterval (-29230107553 / 1000000000000) (-29230103822 / 1000000000000), orderedInterval (51700031220 / 1000000000000) (51700034950 / 1000000000000))
    | 25 => (orderedInterval (25543557276 / 1000000000000) (25543557278 / 1000000000000), orderedInterval (14584209881 / 1000000000000) (14584209883 / 1000000000000))
    | _ => (orderedInterval (33959625490 / 1000000000000) (33959645173 / 1000000000000), orderedInterval (-11982793855 / 1000000000000) (-11982774172 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8056575524 / 1000000000000) (8056575553 / 1000000000000)
      | 1 => orderedInterval (3341172851 / 1000000000000) (3341174946 / 1000000000000)
      | 2 => orderedInterval (163127321 / 1000000000000) (163127720 / 1000000000000)
      | 3 => orderedInterval (8382961507 / 1000000000000) (8382966309 / 1000000000000)
      | 4 => orderedInterval (3290078943 / 1000000000000) (3290079688 / 1000000000000)
      | 5 => orderedInterval (-820513562 / 1000000000000) (-820513514 / 1000000000000)
      | 6 => orderedInterval (4411972188 / 1000000000000) (4411972312 / 1000000000000)
      | 7 => orderedInterval (-2944316556 / 1000000000000) (-2944316506 / 1000000000000)
      | _ => orderedInterval (-8627229966 / 1000000000000) (-8627226140 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16167313815 / 1000000000000) (16167313846 / 1000000000000)
      | 1 => orderedInterval (-2080520016 / 1000000000000) (-2080516756 / 1000000000000)
      | 2 => orderedInterval (1611537596 / 1000000000000) (1611538182 / 1000000000000)
      | 3 => orderedInterval (-14181051386 / 1000000000000) (-14181040789 / 1000000000000)
      | 4 => orderedInterval (-1591238095 / 1000000000000) (-1591236886 / 1000000000000)
      | 5 => orderedInterval (1521684206 / 1000000000000) (1521684274 / 1000000000000)
      | 6 => orderedInterval (6917664195 / 1000000000000) (6917664301 / 1000000000000)
      | 7 => orderedInterval (-1011526314 / 1000000000000) (-1011526269 / 1000000000000)
      | _ => orderedInterval (727481098 / 1000000000000) (727485850 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-8585164000 / 1000000000000) (-8585163963 / 1000000000000)
      | 1 => orderedInterval (-5488902175 / 1000000000000) (-5488897068 / 1000000000000)
      | 2 => orderedInterval (-1728421918 / 1000000000000) (-1728421050 / 1000000000000)
      | 3 => orderedInterval (-37047972227 / 1000000000000) (-37047948462 / 1000000000000)
      | 4 => orderedInterval (-8459490984 / 1000000000000) (-8459488982 / 1000000000000)
      | 5 => orderedInterval (1363876589 / 1000000000000) (1363876687 / 1000000000000)
      | 6 => orderedInterval (-2632761257 / 1000000000000) (-2632761161 / 1000000000000)
      | 7 => orderedInterval (3389556632 / 1000000000000) (3389556677 / 1000000000000)
      | _ => orderedInterval (17052879919 / 1000000000000) (17052885860 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-17186966873 / 1000000000000) (-17186966830 / 1000000000000)
      | 1 => orderedInterval (3086248303 / 1000000000000) (3086256304 / 1000000000000)
      | 2 => orderedInterval (-4928303597 / 1000000000000) (-4928302308 / 1000000000000)
      | 3 => orderedInterval (63422830357 / 1000000000000) (63422884070 / 1000000000000)
      | 4 => orderedInterval (5325681058 / 1000000000000) (5325684440 / 1000000000000)
      | 5 => orderedInterval (-233827596 / 1000000000000) (-233827450 / 1000000000000)
      | 6 => orderedInterval (-7178182229 / 1000000000000) (-7178182139 / 1000000000000)
      | 7 => orderedInterval (1169574987 / 1000000000000) (1169575033 / 1000000000000)
      | _ => orderedInterval (3251741189 / 1000000000000) (3251748632 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9333352187 / 1000000000000) (9333352237 / 1000000000000)
      | 1 => orderedInterval (13115952585 / 1000000000000) (13115965144 / 1000000000000)
      | 2 => orderedInterval (9081660736 / 1000000000000) (9081662667 / 1000000000000)
      | 3 => orderedInterval (180011635981 / 1000000000000) (180011758141 / 1000000000000)
      | 4 => orderedInterval (23457063458 / 1000000000000) (23457069329 / 1000000000000)
      | 5 => orderedInterval (-2362849824 / 1000000000000) (-2362849598 / 1000000000000)
      | 6 => orderedInterval (1869021953 / 1000000000000) (1869022039 / 1000000000000)
      | 7 => orderedInterval (-3972123465 / 1000000000000) (-3972123416 / 1000000000000)
      | _ => orderedInterval (-40041212962 / 1000000000000) (-40041203573 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (15253828250 / 1000000000000) (15253840368 / 1000000000000)
    | 1 => orderedInterval (8081345099 / 1000000000000) (8081365753 / 1000000000000)
    | 2 => orderedInterval (-42136399421 / 1000000000000) (-42136361462 / 1000000000000)
    | 3 => orderedInterval (46728795599 / 1000000000000) (46728869752 / 1000000000000)
    | _ => orderedInterval (190492500649 / 1000000000000) (190492652970 / 1000000000000)

theorem compactCertificate524_stateChecks0 :
    compactCertificate524.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (791 / 2)) (orderedInterval (17248747536 / 1000000000000) (17248747537 / 1000000000000), orderedInterval (36201661361 / 1000000000000) (36201661362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1165294039789691 / 4000000000000)) (orderedInterval (2786222083 / 1000000000000) (2786222086 / 1000000000000), orderedInterval (-46668553523 / 1000000000000) (-46668553519 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (376832149991003 / 800000000000)) (orderedInterval (20344077455 / 1000000000000) (20344077456 / 1000000000000), orderedInterval (30599277590 / 1000000000000) (30599277591 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_stateChecks1 :
    compactCertificate524.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (340029894525937 / 4000000000000)) (orderedInterval (-71305734004 / 1000000000000) (-71305734003 / 1000000000000), orderedInterval (-48615612348 / 1000000000000) (-48615612347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (913368125857789 / 4000000000000)) (orderedInterval (10975062017 / 1000000000000) (10975062077 / 1000000000000), orderedInterval (-51672494729 / 1000000000000) (-51672494668 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2479972137107913 / 4000000000000)) (orderedInterval (-30480384403 / 1000000000000) (-30480355645 / 1000000000000), orderedInterval (9912153249 / 1000000000000) (9912182007 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_stateChecks2 :
    compactCertificate524.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1826736251716369 / 4000000000000)) (orderedInterval (-34843953399 / 1000000000000) (-34843931431 / 1000000000000), orderedInterval (13450960803 / 1000000000000) (13450982772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3130143703038037 / 4000000000000)) (orderedInterval (-24945563232 / 1000000000000) (-24945563229 / 1000000000000), orderedInterval (-13813487341 / 1000000000000) (-13813487338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2305649684470783 / 4000000000000)) (orderedInterval (-25086600752 / 1000000000000) (-25086585228 / 1000000000000), orderedInterval (21818877799 / 1000000000000) (21818893322 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_stateChecks3 :
    compactCertificate524.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (3537459540404209 / 4000000000000)) (orderedInterval (-18849801055 / 1000000000000) (-18849799730 / 1000000000000), orderedInterval (19103744479 / 1000000000000) (19103745804 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2042353217899561 / 4000000000000)) (orderedInterval (22913200416 / 1000000000000) (22913205240 / 1000000000000), orderedInterval (-26889167360 / 1000000000000) (-26889162536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (3624191625037949 / 4000000000000)) (orderedInterval (23466492459 / 1000000000000) (23466520969 / 1000000000000), orderedInterval (-12340034394 / 1000000000000) (-12340005884 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_stateChecks4 :
    compactCertificate524.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3386189933883281 / 4000000000000)) (orderedInterval (-21434744082 / 1000000000000) (-21434738084 / 1000000000000), orderedInterval (17117358734 / 1000000000000) (17117364732 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2416544916472673 / 4000000000000)) (orderedInterval (32021790101 / 1000000000000) (32021796334 / 1000000000000), orderedInterval (-5353135042 / 1000000000000) (-5353128809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2740104377573367 / 4000000000000)) (orderedInterval (24692139695 / 1000000000000) (24692139696 / 1000000000000), orderedInterval (17860307368 / 1000000000000) (17860307369 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_stateChecks5 :
    compactCertificate524.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2284413359778823 / 4000000000000)) (orderedInterval (3952335338 / 1000000000000) (3952335339 / 1000000000000), orderedInterval (33149194388 / 1000000000000) (33149194389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2018348482671283 / 4000000000000)) (orderedInterval (14617960772 / 1000000000000) (14617960944 / 1000000000000), orderedInterval (-32387009880 / 1000000000000) (-32387009707 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (584996059189017 / 800000000000)) (orderedInterval (-1156715182 / 1000000000000) (-1156715181 / 1000000000000), orderedInterval (-29482411403 / 1000000000000) (-29482411402 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_stateChecks6 :
    compactCertificate524.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1618129886372699 / 4000000000000)) (orderedInterval (-2066211454 / 1000000000000) (-2066211453 / 1000000000000), orderedInterval (-39613722172 / 1000000000000) (-39613722171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1371706624975939 / 4000000000000)) (orderedInterval (-41253697176 / 1000000000000) (-41253697174 / 1000000000000), orderedInterval (-12372151659 / 1000000000000) (-12372151656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (858350315529217 / 4000000000000)) (orderedInterval (53651625201 / 1000000000000) (53651625953 / 1000000000000), orderedInterval (-9516951681 / 1000000000000) (-9516950928 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_stateChecks7 :
    compactCertificate524.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (461623654435839 / 4000000000000)) (orderedInterval (3615570451 / 1000000000000) (3615570464 / 1000000000000), orderedInterval (-74200112115 / 1000000000000) (-74200112103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1253398020384517 / 4000000000000)) (orderedInterval (-1115961743 / 1000000000000) (-1115961741 / 1000000000000), orderedInterval (45061935880 / 1000000000000) (45061935882 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1711407840542309 / 4000000000000)) (orderedInterval (37877284317 / 1000000000000) (37877284339 / 1000000000000), orderedInterval (7253298497 / 1000000000000) (7253298519 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_stateChecks8 :
    compactCertificate524.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (723649684470783 / 4000000000000)) (orderedInterval (-29230107553 / 1000000000000) (-29230103822 / 1000000000000), orderedInterval (51700031220 / 1000000000000) (51700034950 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2941595791544543 / 4000000000000)) (orderedInterval (25543557276 / 1000000000000) (25543557278 / 1000000000000), orderedInterval (14584209881 / 1000000000000) (14584209883 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1964849663249137 / 4000000000000)) (orderedInterval (33959625490 / 1000000000000) (33959645173 / 1000000000000), orderedInterval (-11982793855 / 1000000000000) (-11982774172 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_states : ∀ j,
    BesselStateValid (compactCertificate524.point j) (compactCertificate524.state j) :=
  compactCertificate524.statesValid_of_checks3 compactCertificate524_stateChecks0
    compactCertificate524_stateChecks1 compactCertificate524_stateChecks2
    compactCertificate524_stateChecks3 compactCertificate524_stateChecks4
    compactCertificate524_stateChecks5 compactCertificate524_stateChecks6
    compactCertificate524_stateChecks7 compactCertificate524_stateChecks8

theorem compactCertificate524_chunkChecks0_0 :
    compactCertificate524.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (791 / 2) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17248747536 / 1000000000000) (17248747537 / 1000000000000), orderedInterval (36201661361 / 1000000000000) (36201661362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1165294039789691 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2786222083 / 1000000000000) (2786222086 / 1000000000000), orderedInterval (-46668553523 / 1000000000000) (-46668553519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (376832149991003 / 800000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20344077455 / 1000000000000) (20344077456 / 1000000000000), orderedInterval (30599277590 / 1000000000000) (30599277591 / 1000000000000)))) (orderedInterval (8056575524 / 1000000000000) (8056575553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (340029894525937 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71305734004 / 1000000000000) (-71305734003 / 1000000000000), orderedInterval (-48615612348 / 1000000000000) (-48615612347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (913368125857789 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10975062017 / 1000000000000) (10975062077 / 1000000000000), orderedInterval (-51672494729 / 1000000000000) (-51672494668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2479972137107913 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30480384403 / 1000000000000) (-30480355645 / 1000000000000), orderedInterval (9912153249 / 1000000000000) (9912182007 / 1000000000000)))) (orderedInterval (3341172851 / 1000000000000) (3341174946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1826736251716369 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34843953399 / 1000000000000) (-34843931431 / 1000000000000), orderedInterval (13450960803 / 1000000000000) (13450982772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3130143703038037 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24945563232 / 1000000000000) (-24945563229 / 1000000000000), orderedInterval (-13813487341 / 1000000000000) (-13813487338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2305649684470783 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25086600752 / 1000000000000) (-25086585228 / 1000000000000), orderedInterval (21818877799 / 1000000000000) (21818893322 / 1000000000000)))) (orderedInterval (163127321 / 1000000000000) (163127720 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks0_1 :
    compactCertificate524.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3537459540404209 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18849801055 / 1000000000000) (-18849799730 / 1000000000000), orderedInterval (19103744479 / 1000000000000) (19103745804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2042353217899561 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22913200416 / 1000000000000) (22913205240 / 1000000000000), orderedInterval (-26889167360 / 1000000000000) (-26889162536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3624191625037949 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23466492459 / 1000000000000) (23466520969 / 1000000000000), orderedInterval (-12340034394 / 1000000000000) (-12340005884 / 1000000000000)))) (orderedInterval (8382961507 / 1000000000000) (8382966309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3386189933883281 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21434744082 / 1000000000000) (-21434738084 / 1000000000000), orderedInterval (17117358734 / 1000000000000) (17117364732 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2416544916472673 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32021790101 / 1000000000000) (32021796334 / 1000000000000), orderedInterval (-5353135042 / 1000000000000) (-5353128809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2740104377573367 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24692139695 / 1000000000000) (24692139696 / 1000000000000), orderedInterval (17860307368 / 1000000000000) (17860307369 / 1000000000000)))) (orderedInterval (3290078943 / 1000000000000) (3290079688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2284413359778823 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3952335338 / 1000000000000) (3952335339 / 1000000000000), orderedInterval (33149194388 / 1000000000000) (33149194389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2018348482671283 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14617960772 / 1000000000000) (14617960944 / 1000000000000), orderedInterval (-32387009880 / 1000000000000) (-32387009707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (584996059189017 / 800000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1156715182 / 1000000000000) (-1156715181 / 1000000000000), orderedInterval (-29482411403 / 1000000000000) (-29482411402 / 1000000000000)))) (orderedInterval (-820513562 / 1000000000000) (-820513514 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks0_2 :
    compactCertificate524.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1618129886372699 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2066211454 / 1000000000000) (-2066211453 / 1000000000000), orderedInterval (-39613722172 / 1000000000000) (-39613722171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1371706624975939 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41253697176 / 1000000000000) (-41253697174 / 1000000000000), orderedInterval (-12372151659 / 1000000000000) (-12372151656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (858350315529217 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53651625201 / 1000000000000) (53651625953 / 1000000000000), orderedInterval (-9516951681 / 1000000000000) (-9516950928 / 1000000000000)))) (orderedInterval (4411972188 / 1000000000000) (4411972312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (461623654435839 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (3615570451 / 1000000000000) (3615570464 / 1000000000000), orderedInterval (-74200112115 / 1000000000000) (-74200112103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1253398020384517 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1115961743 / 1000000000000) (-1115961741 / 1000000000000), orderedInterval (45061935880 / 1000000000000) (45061935882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1711407840542309 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37877284317 / 1000000000000) (37877284339 / 1000000000000), orderedInterval (7253298497 / 1000000000000) (7253298519 / 1000000000000)))) (orderedInterval (-2944316556 / 1000000000000) (-2944316506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (723649684470783 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29230107553 / 1000000000000) (-29230103822 / 1000000000000), orderedInterval (51700031220 / 1000000000000) (51700034950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2941595791544543 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25543557276 / 1000000000000) (25543557278 / 1000000000000), orderedInterval (14584209881 / 1000000000000) (14584209883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1964849663249137 / 4000000000000) 0 (IntervalRat.scale (791 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33959625490 / 1000000000000) (33959645173 / 1000000000000), orderedInterval (-11982793855 / 1000000000000) (-11982774172 / 1000000000000)))) (orderedInterval (-8627229966 / 1000000000000) (-8627226140 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks0 :
    compactCertificate524.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate524.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate524_chunkChecks0_0
    compactCertificate524_chunkChecks0_1 compactCertificate524_chunkChecks0_2

theorem compactCertificate524_chunkChecks1_0 :
    compactCertificate524.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (791 / 2) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17248747536 / 1000000000000) (17248747537 / 1000000000000), orderedInterval (36201661361 / 1000000000000) (36201661362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1165294039789691 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2786222083 / 1000000000000) (2786222086 / 1000000000000), orderedInterval (-46668553523 / 1000000000000) (-46668553519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (376832149991003 / 800000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20344077455 / 1000000000000) (20344077456 / 1000000000000), orderedInterval (30599277590 / 1000000000000) (30599277591 / 1000000000000)))) (orderedInterval (16167313815 / 1000000000000) (16167313846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (340029894525937 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71305734004 / 1000000000000) (-71305734003 / 1000000000000), orderedInterval (-48615612348 / 1000000000000) (-48615612347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (913368125857789 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10975062017 / 1000000000000) (10975062077 / 1000000000000), orderedInterval (-51672494729 / 1000000000000) (-51672494668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2479972137107913 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30480384403 / 1000000000000) (-30480355645 / 1000000000000), orderedInterval (9912153249 / 1000000000000) (9912182007 / 1000000000000)))) (orderedInterval (-2080520016 / 1000000000000) (-2080516756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1826736251716369 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34843953399 / 1000000000000) (-34843931431 / 1000000000000), orderedInterval (13450960803 / 1000000000000) (13450982772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3130143703038037 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24945563232 / 1000000000000) (-24945563229 / 1000000000000), orderedInterval (-13813487341 / 1000000000000) (-13813487338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2305649684470783 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25086600752 / 1000000000000) (-25086585228 / 1000000000000), orderedInterval (21818877799 / 1000000000000) (21818893322 / 1000000000000)))) (orderedInterval (1611537596 / 1000000000000) (1611538182 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks1_1 :
    compactCertificate524.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3537459540404209 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18849801055 / 1000000000000) (-18849799730 / 1000000000000), orderedInterval (19103744479 / 1000000000000) (19103745804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2042353217899561 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22913200416 / 1000000000000) (22913205240 / 1000000000000), orderedInterval (-26889167360 / 1000000000000) (-26889162536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3624191625037949 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23466492459 / 1000000000000) (23466520969 / 1000000000000), orderedInterval (-12340034394 / 1000000000000) (-12340005884 / 1000000000000)))) (orderedInterval (-14181051386 / 1000000000000) (-14181040789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3386189933883281 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21434744082 / 1000000000000) (-21434738084 / 1000000000000), orderedInterval (17117358734 / 1000000000000) (17117364732 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2416544916472673 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32021790101 / 1000000000000) (32021796334 / 1000000000000), orderedInterval (-5353135042 / 1000000000000) (-5353128809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2740104377573367 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24692139695 / 1000000000000) (24692139696 / 1000000000000), orderedInterval (17860307368 / 1000000000000) (17860307369 / 1000000000000)))) (orderedInterval (-1591238095 / 1000000000000) (-1591236886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2284413359778823 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3952335338 / 1000000000000) (3952335339 / 1000000000000), orderedInterval (33149194388 / 1000000000000) (33149194389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2018348482671283 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14617960772 / 1000000000000) (14617960944 / 1000000000000), orderedInterval (-32387009880 / 1000000000000) (-32387009707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (584996059189017 / 800000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1156715182 / 1000000000000) (-1156715181 / 1000000000000), orderedInterval (-29482411403 / 1000000000000) (-29482411402 / 1000000000000)))) (orderedInterval (1521684206 / 1000000000000) (1521684274 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks1_2 :
    compactCertificate524.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1618129886372699 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2066211454 / 1000000000000) (-2066211453 / 1000000000000), orderedInterval (-39613722172 / 1000000000000) (-39613722171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1371706624975939 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41253697176 / 1000000000000) (-41253697174 / 1000000000000), orderedInterval (-12372151659 / 1000000000000) (-12372151656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (858350315529217 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53651625201 / 1000000000000) (53651625953 / 1000000000000), orderedInterval (-9516951681 / 1000000000000) (-9516950928 / 1000000000000)))) (orderedInterval (6917664195 / 1000000000000) (6917664301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (461623654435839 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (3615570451 / 1000000000000) (3615570464 / 1000000000000), orderedInterval (-74200112115 / 1000000000000) (-74200112103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1253398020384517 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1115961743 / 1000000000000) (-1115961741 / 1000000000000), orderedInterval (45061935880 / 1000000000000) (45061935882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1711407840542309 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37877284317 / 1000000000000) (37877284339 / 1000000000000), orderedInterval (7253298497 / 1000000000000) (7253298519 / 1000000000000)))) (orderedInterval (-1011526314 / 1000000000000) (-1011526269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (723649684470783 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29230107553 / 1000000000000) (-29230103822 / 1000000000000), orderedInterval (51700031220 / 1000000000000) (51700034950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2941595791544543 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25543557276 / 1000000000000) (25543557278 / 1000000000000), orderedInterval (14584209881 / 1000000000000) (14584209883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1964849663249137 / 4000000000000) 1 (IntervalRat.scale (791 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33959625490 / 1000000000000) (33959645173 / 1000000000000), orderedInterval (-11982793855 / 1000000000000) (-11982774172 / 1000000000000)))) (orderedInterval (727481098 / 1000000000000) (727485850 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks1 :
    compactCertificate524.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate524.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate524_chunkChecks1_0
    compactCertificate524_chunkChecks1_1 compactCertificate524_chunkChecks1_2

theorem compactCertificate524_chunkChecks2_0 :
    compactCertificate524.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (791 / 2) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17248747536 / 1000000000000) (17248747537 / 1000000000000), orderedInterval (36201661361 / 1000000000000) (36201661362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1165294039789691 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2786222083 / 1000000000000) (2786222086 / 1000000000000), orderedInterval (-46668553523 / 1000000000000) (-46668553519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (376832149991003 / 800000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20344077455 / 1000000000000) (20344077456 / 1000000000000), orderedInterval (30599277590 / 1000000000000) (30599277591 / 1000000000000)))) (orderedInterval (-8585164000 / 1000000000000) (-8585163963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (340029894525937 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71305734004 / 1000000000000) (-71305734003 / 1000000000000), orderedInterval (-48615612348 / 1000000000000) (-48615612347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (913368125857789 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10975062017 / 1000000000000) (10975062077 / 1000000000000), orderedInterval (-51672494729 / 1000000000000) (-51672494668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2479972137107913 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30480384403 / 1000000000000) (-30480355645 / 1000000000000), orderedInterval (9912153249 / 1000000000000) (9912182007 / 1000000000000)))) (orderedInterval (-5488902175 / 1000000000000) (-5488897068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1826736251716369 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34843953399 / 1000000000000) (-34843931431 / 1000000000000), orderedInterval (13450960803 / 1000000000000) (13450982772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3130143703038037 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24945563232 / 1000000000000) (-24945563229 / 1000000000000), orderedInterval (-13813487341 / 1000000000000) (-13813487338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2305649684470783 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25086600752 / 1000000000000) (-25086585228 / 1000000000000), orderedInterval (21818877799 / 1000000000000) (21818893322 / 1000000000000)))) (orderedInterval (-1728421918 / 1000000000000) (-1728421050 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks2_1 :
    compactCertificate524.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3537459540404209 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18849801055 / 1000000000000) (-18849799730 / 1000000000000), orderedInterval (19103744479 / 1000000000000) (19103745804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2042353217899561 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22913200416 / 1000000000000) (22913205240 / 1000000000000), orderedInterval (-26889167360 / 1000000000000) (-26889162536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3624191625037949 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23466492459 / 1000000000000) (23466520969 / 1000000000000), orderedInterval (-12340034394 / 1000000000000) (-12340005884 / 1000000000000)))) (orderedInterval (-37047972227 / 1000000000000) (-37047948462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3386189933883281 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21434744082 / 1000000000000) (-21434738084 / 1000000000000), orderedInterval (17117358734 / 1000000000000) (17117364732 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2416544916472673 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32021790101 / 1000000000000) (32021796334 / 1000000000000), orderedInterval (-5353135042 / 1000000000000) (-5353128809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2740104377573367 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24692139695 / 1000000000000) (24692139696 / 1000000000000), orderedInterval (17860307368 / 1000000000000) (17860307369 / 1000000000000)))) (orderedInterval (-8459490984 / 1000000000000) (-8459488982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2284413359778823 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3952335338 / 1000000000000) (3952335339 / 1000000000000), orderedInterval (33149194388 / 1000000000000) (33149194389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2018348482671283 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14617960772 / 1000000000000) (14617960944 / 1000000000000), orderedInterval (-32387009880 / 1000000000000) (-32387009707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (584996059189017 / 800000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1156715182 / 1000000000000) (-1156715181 / 1000000000000), orderedInterval (-29482411403 / 1000000000000) (-29482411402 / 1000000000000)))) (orderedInterval (1363876589 / 1000000000000) (1363876687 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks2_2 :
    compactCertificate524.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1618129886372699 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2066211454 / 1000000000000) (-2066211453 / 1000000000000), orderedInterval (-39613722172 / 1000000000000) (-39613722171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1371706624975939 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41253697176 / 1000000000000) (-41253697174 / 1000000000000), orderedInterval (-12372151659 / 1000000000000) (-12372151656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (858350315529217 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53651625201 / 1000000000000) (53651625953 / 1000000000000), orderedInterval (-9516951681 / 1000000000000) (-9516950928 / 1000000000000)))) (orderedInterval (-2632761257 / 1000000000000) (-2632761161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (461623654435839 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (3615570451 / 1000000000000) (3615570464 / 1000000000000), orderedInterval (-74200112115 / 1000000000000) (-74200112103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1253398020384517 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1115961743 / 1000000000000) (-1115961741 / 1000000000000), orderedInterval (45061935880 / 1000000000000) (45061935882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1711407840542309 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37877284317 / 1000000000000) (37877284339 / 1000000000000), orderedInterval (7253298497 / 1000000000000) (7253298519 / 1000000000000)))) (orderedInterval (3389556632 / 1000000000000) (3389556677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (723649684470783 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29230107553 / 1000000000000) (-29230103822 / 1000000000000), orderedInterval (51700031220 / 1000000000000) (51700034950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2941595791544543 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25543557276 / 1000000000000) (25543557278 / 1000000000000), orderedInterval (14584209881 / 1000000000000) (14584209883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1964849663249137 / 4000000000000) 2 (IntervalRat.scale (791 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33959625490 / 1000000000000) (33959645173 / 1000000000000), orderedInterval (-11982793855 / 1000000000000) (-11982774172 / 1000000000000)))) (orderedInterval (17052879919 / 1000000000000) (17052885860 / 1000000000000))) = true
  rfl'

theorem compactCertificate524_chunkChecks2 :
    compactCertificate524.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate524.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate524_chunkChecks2_0
    compactCertificate524_chunkChecks2_1 compactCertificate524_chunkChecks2_2

theorem compactCertificate524_chunkChecks3_0 :
    compactCertificate524.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (791 / 2) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17248747536 / 1000000000000) (17248747537 / 1000000000000), orderedInterval (36201661361 / 1000000000000) (36201661362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1165294039789691 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2786222083 / 1000000000000) (2786222086 / 1000000000000), orderedInterval (-46668553523 / 1000000000000) (-46668553519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (376832149991003 / 800000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20344077455 / 1000000000000) (20344077456 / 1000000000000), orderedInterval (30599277590 / 1000000000000) (30599277591 / 1000000000000)))) (orderedInterval (-17186966873 / 1000000000000) (-17186966830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (340029894525937 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71305734004 / 1000000000000) (-71305734003 / 1000000000000), orderedInterval (-48615612348 / 1000000000000) (-48615612347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (913368125857789 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10975062017 / 1000000000000) (10975062077 / 1000000000000), orderedInterval (-51672494729 / 1000000000000) (-51672494668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2479972137107913 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30480384403 / 1000000000000) (-30480355645 / 1000000000000), orderedInterval (9912153249 / 1000000000000) (9912182007 / 1000000000000)))) (orderedInterval (3086248303 / 1000000000000) (3086256304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1826736251716369 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34843953399 / 1000000000000) (-34843931431 / 1000000000000), orderedInterval (13450960803 / 1000000000000) (13450982772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3130143703038037 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24945563232 / 1000000000000) (-24945563229 / 1000000000000), orderedInterval (-13813487341 / 1000000000000) (-13813487338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2305649684470783 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25086600752 / 1000000000000) (-25086585228 / 1000000000000), orderedInterval (21818877799 / 1000000000000) (21818893322 / 1000000000000)))) (orderedInterval (-4928303597 / 1000000000000) (-4928302308 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate524_chunkChecks3_1 :
    compactCertificate524.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3537459540404209 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18849801055 / 1000000000000) (-18849799730 / 1000000000000), orderedInterval (19103744479 / 1000000000000) (19103745804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2042353217899561 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22913200416 / 1000000000000) (22913205240 / 1000000000000), orderedInterval (-26889167360 / 1000000000000) (-26889162536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3624191625037949 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23466492459 / 1000000000000) (23466520969 / 1000000000000), orderedInterval (-12340034394 / 1000000000000) (-12340005884 / 1000000000000)))) (orderedInterval (63422830357 / 1000000000000) (63422884070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3386189933883281 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21434744082 / 1000000000000) (-21434738084 / 1000000000000), orderedInterval (17117358734 / 1000000000000) (17117364732 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2416544916472673 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32021790101 / 1000000000000) (32021796334 / 1000000000000), orderedInterval (-5353135042 / 1000000000000) (-5353128809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2740104377573367 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24692139695 / 1000000000000) (24692139696 / 1000000000000), orderedInterval (17860307368 / 1000000000000) (17860307369 / 1000000000000)))) (orderedInterval (5325681058 / 1000000000000) (5325684440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2284413359778823 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3952335338 / 1000000000000) (3952335339 / 1000000000000), orderedInterval (33149194388 / 1000000000000) (33149194389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2018348482671283 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14617960772 / 1000000000000) (14617960944 / 1000000000000), orderedInterval (-32387009880 / 1000000000000) (-32387009707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (584996059189017 / 800000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1156715182 / 1000000000000) (-1156715181 / 1000000000000), orderedInterval (-29482411403 / 1000000000000) (-29482411402 / 1000000000000)))) (orderedInterval (-233827596 / 1000000000000) (-233827450 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate524_chunkChecks3_2 :
    compactCertificate524.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1618129886372699 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2066211454 / 1000000000000) (-2066211453 / 1000000000000), orderedInterval (-39613722172 / 1000000000000) (-39613722171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1371706624975939 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41253697176 / 1000000000000) (-41253697174 / 1000000000000), orderedInterval (-12372151659 / 1000000000000) (-12372151656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (858350315529217 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53651625201 / 1000000000000) (53651625953 / 1000000000000), orderedInterval (-9516951681 / 1000000000000) (-9516950928 / 1000000000000)))) (orderedInterval (-7178182229 / 1000000000000) (-7178182139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (461623654435839 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (3615570451 / 1000000000000) (3615570464 / 1000000000000), orderedInterval (-74200112115 / 1000000000000) (-74200112103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1253398020384517 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1115961743 / 1000000000000) (-1115961741 / 1000000000000), orderedInterval (45061935880 / 1000000000000) (45061935882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1711407840542309 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37877284317 / 1000000000000) (37877284339 / 1000000000000), orderedInterval (7253298497 / 1000000000000) (7253298519 / 1000000000000)))) (orderedInterval (1169574987 / 1000000000000) (1169575033 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (723649684470783 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29230107553 / 1000000000000) (-29230103822 / 1000000000000), orderedInterval (51700031220 / 1000000000000) (51700034950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2941595791544543 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25543557276 / 1000000000000) (25543557278 / 1000000000000), orderedInterval (14584209881 / 1000000000000) (14584209883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1964849663249137 / 4000000000000) 3 (IntervalRat.scale (791 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33959625490 / 1000000000000) (33959645173 / 1000000000000), orderedInterval (-11982793855 / 1000000000000) (-11982774172 / 1000000000000)))) (orderedInterval (3251741189 / 1000000000000) (3251748632 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate524_chunkChecks3 :
    compactCertificate524.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate524.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate524_chunkChecks3_0
    compactCertificate524_chunkChecks3_1 compactCertificate524_chunkChecks3_2

theorem compactCertificate524_chunkChecks4_0 :
    compactCertificate524.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (791 / 2) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17248747536 / 1000000000000) (17248747537 / 1000000000000), orderedInterval (36201661361 / 1000000000000) (36201661362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1165294039789691 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2786222083 / 1000000000000) (2786222086 / 1000000000000), orderedInterval (-46668553523 / 1000000000000) (-46668553519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (376832149991003 / 800000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20344077455 / 1000000000000) (20344077456 / 1000000000000), orderedInterval (30599277590 / 1000000000000) (30599277591 / 1000000000000)))) (orderedInterval (9333352187 / 1000000000000) (9333352237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (340029894525937 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71305734004 / 1000000000000) (-71305734003 / 1000000000000), orderedInterval (-48615612348 / 1000000000000) (-48615612347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (913368125857789 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10975062017 / 1000000000000) (10975062077 / 1000000000000), orderedInterval (-51672494729 / 1000000000000) (-51672494668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2479972137107913 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30480384403 / 1000000000000) (-30480355645 / 1000000000000), orderedInterval (9912153249 / 1000000000000) (9912182007 / 1000000000000)))) (orderedInterval (13115952585 / 1000000000000) (13115965144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1826736251716369 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34843953399 / 1000000000000) (-34843931431 / 1000000000000), orderedInterval (13450960803 / 1000000000000) (13450982772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3130143703038037 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24945563232 / 1000000000000) (-24945563229 / 1000000000000), orderedInterval (-13813487341 / 1000000000000) (-13813487338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2305649684470783 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25086600752 / 1000000000000) (-25086585228 / 1000000000000), orderedInterval (21818877799 / 1000000000000) (21818893322 / 1000000000000)))) (orderedInterval (9081660736 / 1000000000000) (9081662667 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate524_chunkChecks4_1 :
    compactCertificate524.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3537459540404209 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18849801055 / 1000000000000) (-18849799730 / 1000000000000), orderedInterval (19103744479 / 1000000000000) (19103745804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2042353217899561 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22913200416 / 1000000000000) (22913205240 / 1000000000000), orderedInterval (-26889167360 / 1000000000000) (-26889162536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3624191625037949 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23466492459 / 1000000000000) (23466520969 / 1000000000000), orderedInterval (-12340034394 / 1000000000000) (-12340005884 / 1000000000000)))) (orderedInterval (180011635981 / 1000000000000) (180011758141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3386189933883281 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21434744082 / 1000000000000) (-21434738084 / 1000000000000), orderedInterval (17117358734 / 1000000000000) (17117364732 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2416544916472673 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32021790101 / 1000000000000) (32021796334 / 1000000000000), orderedInterval (-5353135042 / 1000000000000) (-5353128809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2740104377573367 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24692139695 / 1000000000000) (24692139696 / 1000000000000), orderedInterval (17860307368 / 1000000000000) (17860307369 / 1000000000000)))) (orderedInterval (23457063458 / 1000000000000) (23457069329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2284413359778823 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3952335338 / 1000000000000) (3952335339 / 1000000000000), orderedInterval (33149194388 / 1000000000000) (33149194389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2018348482671283 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14617960772 / 1000000000000) (14617960944 / 1000000000000), orderedInterval (-32387009880 / 1000000000000) (-32387009707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (584996059189017 / 800000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1156715182 / 1000000000000) (-1156715181 / 1000000000000), orderedInterval (-29482411403 / 1000000000000) (-29482411402 / 1000000000000)))) (orderedInterval (-2362849824 / 1000000000000) (-2362849598 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate524_chunkChecks4_2 :
    compactCertificate524.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1618129886372699 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2066211454 / 1000000000000) (-2066211453 / 1000000000000), orderedInterval (-39613722172 / 1000000000000) (-39613722171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1371706624975939 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41253697176 / 1000000000000) (-41253697174 / 1000000000000), orderedInterval (-12372151659 / 1000000000000) (-12372151656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (858350315529217 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53651625201 / 1000000000000) (53651625953 / 1000000000000), orderedInterval (-9516951681 / 1000000000000) (-9516950928 / 1000000000000)))) (orderedInterval (1869021953 / 1000000000000) (1869022039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (461623654435839 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (3615570451 / 1000000000000) (3615570464 / 1000000000000), orderedInterval (-74200112115 / 1000000000000) (-74200112103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1253398020384517 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-1115961743 / 1000000000000) (-1115961741 / 1000000000000), orderedInterval (45061935880 / 1000000000000) (45061935882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1711407840542309 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37877284317 / 1000000000000) (37877284339 / 1000000000000), orderedInterval (7253298497 / 1000000000000) (7253298519 / 1000000000000)))) (orderedInterval (-3972123465 / 1000000000000) (-3972123416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (723649684470783 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29230107553 / 1000000000000) (-29230103822 / 1000000000000), orderedInterval (51700031220 / 1000000000000) (51700034950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2941595791544543 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25543557276 / 1000000000000) (25543557278 / 1000000000000), orderedInterval (14584209881 / 1000000000000) (14584209883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1964849663249137 / 4000000000000) 4 (IntervalRat.scale (791 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33959625490 / 1000000000000) (33959645173 / 1000000000000), orderedInterval (-11982793855 / 1000000000000) (-11982774172 / 1000000000000)))) (orderedInterval (-40041212962 / 1000000000000) (-40041203573 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate524_chunkChecks4 :
    compactCertificate524.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate524.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate524_chunkChecks4_0
    compactCertificate524_chunkChecks4_1 compactCertificate524_chunkChecks4_2

theorem compactCertificate524_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate524.chunkCheck r b = true :=
  compactCertificate524.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate524_chunkChecks0
    · exact compactCertificate524_chunkChecks1
    · exact compactCertificate524_chunkChecks2
    · exact compactCertificate524_chunkChecks3
    · exact compactCertificate524_chunkChecks4)

theorem compactCertificate524_coefficient0 :
    compactCertificate524.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate524_coefficient1 :
    compactCertificate524.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate524_coefficient2 :
    compactCertificate524.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate524_coefficient3 :
    compactCertificate524.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate524_coefficient4 :
    compactCertificate524.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate524_coefficients : ∀ r : Fin 5,
    compactCertificate524.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate524_coefficient0
  · exact compactCertificate524_coefficient1
  · exact compactCertificate524_coefficient2
  · exact compactCertificate524_coefficient3
  · exact compactCertificate524_coefficient4

theorem compactCertificate524_lower : (1 : ℚ) ≤ compactCertificate524.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate524, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate524_proves {t : ℝ} (ht : t ∈ compactCertificate524.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate524.proves compactCertificate524_states compactCertificate524_chunks
    compactCertificate524_coefficients compactCertificate524_lower ht

end Erdos232
