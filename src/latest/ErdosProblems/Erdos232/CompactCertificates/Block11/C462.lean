/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate462 : CompactCertificate where
  left := 333
  right := 334
  center := 667 / 2
  grid := fun i =>
    match i.val with
    | 0 => 106
    | 1 => 78
    | 2 => 126
    | 3 => 23
    | 4 => 61
    | 5 => 166
    | 6 => 123
    | 7 => 210
    | 8 => 155
    | 9 => 237
    | 10 => 137
    | 11 => 243
    | 12 => 227
    | 13 => 162
    | 14 => 184
    | 15 => 153
    | 16 => 136
    | 17 => 196
    | 18 => 109
    | 19 => 92
    | 20 => 58
    | 21 => 31
    | 22 => 84
    | 23 => 115
    | 24 => 49
    | 25 => 197
    | _ => 132
  point := fun i =>
    match i.val with
    | 0 => 667 / 2
    | 1 => 982618362249967 / 4000000000000
    | 2 => 317758589183311 / 800000000000
    | 3 => 286725587419469 / 4000000000000
    | 4 => 770185259098793 / 4000000000000
    | 5 => 2091202800822981 / 4000000000000
    | 6 => 1540370518198253 / 4000000000000
    | 7 => 2639451137707169 / 4000000000000
    | 8 => 1944207761747171 / 4000000000000
    | 9 => 2982914681984333 / 4000000000000
    | 10 => 1722186594613157 / 4000000000000
    | 11 => 3056050333628713 / 4000000000000
    | 12 => 2855358642098797 / 4000000000000
    | 13 => 2037718659023101 / 4000000000000
    | 14 => 2310555777296379 / 4000000000000
    | 15 => 1926300519560651 / 4000000000000
    | 16 => 1701944927865671 / 4000000000000
    | 17 => 493289976585429 / 800000000000
    | 18 => 1364466035664463 / 4000000000000
    | 19 => 1156672969480343 / 4000000000000
    | 20 => 723792238252829 / 4000000000000
    | 21 => 389257872956643 / 4000000000000
    | 22 => 1056910846518929 / 4000000000000
    | 23 => 1443121402834033 / 4000000000000
    | 24 => 610207761747171 / 4000000000000
    | 25 => 2480460673780291 / 4000000000000
    | _ => 1656832775457869 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (41808784683 / 1000000000000) (41808784685 / 1000000000000), orderedInterval (12623082147 / 1000000000000) (12623082150 / 1000000000000))
    | 1 => (orderedInterval (50124611353 / 1000000000000) (50124611360 / 1000000000000), orderedInterval (8788552502 / 1000000000000) (8788552509 / 1000000000000))
    | 2 => (orderedInterval (33665164371 / 1000000000000) (33665266934 / 1000000000000), orderedInterval (-21708728183 / 1000000000000) (-21708625620 / 1000000000000))
    | 3 => (orderedInterval (-19499472009 / 1000000000000) (-19499472008 / 1000000000000), orderedInterval (-92065994173 / 1000000000000) (-92065994172 / 1000000000000))
    | 4 => (orderedInterval (-57065283638 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546019 / 1000000000000) (7209546369 / 1000000000000))
    | 5 => (orderedInterval (30443341599 / 1000000000000) (30443446290 / 1000000000000), orderedInterval (-17085240242 / 1000000000000) (-17085135552 / 1000000000000))
    | 6 => (orderedInterval (20841241370 / 1000000000000) (20841242898 / 1000000000000), orderedInterval (-34938425546 / 1000000000000) (-34938424019 / 1000000000000))
    | 7 => (orderedInterval (24589901595 / 1000000000000) (24589901596 / 1000000000000), orderedInterval (18958002036 / 1000000000000) (18958002037 / 1000000000000))
    | 8 => (orderedInterval (3965050114 / 1000000000000) (3965050116 / 1000000000000), orderedInterval (-35977072879 / 1000000000000) (-35977072877 / 1000000000000))
    | 9 => (orderedInterval (-27072094947 / 1000000000000) (-27072000275 / 1000000000000), orderedInterval (11008655864 / 1000000000000) (11008750536 / 1000000000000))
    | 10 => (orderedInterval (-30906372759 / 1000000000000) (-30906372758 / 1000000000000), orderedInterval (-22842639060 / 1000000000000) (-22842639059 / 1000000000000))
    | 11 => (orderedInterval (-28399873494 / 1000000000000) (-28399873201 / 1000000000000), orderedInterval (-5149126985 / 1000000000000) (-5149126692 / 1000000000000))
    | 12 => (orderedInterval (-29749324398 / 1000000000000) (-29749323715 / 1000000000000), orderedInterval (-2587247546 / 1000000000000) (-2587246863 / 1000000000000))
    | 13 => (orderedInterval (33833988836 / 1000000000000) (33833988844 / 1000000000000), orderedInterval (10210437907 / 1000000000000) (10210437916 / 1000000000000))
    | 14 => (orderedInterval (12038257652 / 1000000000000) (12038257653 / 1000000000000), orderedInterval (30928025030 / 1000000000000) (30928025031 / 1000000000000))
    | 15 => (orderedInterval (-36071362386 / 1000000000000) (-36071360291 / 1000000000000), orderedInterval (4599179686 / 1000000000000) (4599181781 / 1000000000000))
    | 16 => (orderedInterval (-32237461672 / 1000000000000) (-32237362868 / 1000000000000), orderedInterval (21414591827 / 1000000000000) (21414690631 / 1000000000000))
    | 17 => (orderedInterval (32042078051 / 1000000000000) (32042080593 / 1000000000000), orderedInterval (-2424303703 / 1000000000000) (-2424301161 / 1000000000000))
    | 18 => (orderedInterval (21915961740 / 1000000000000) (21915963577 / 1000000000000), orderedInterval (-37260797194 / 1000000000000) (-37260795358 / 1000000000000))
    | 19 => (orderedInterval (37519345683 / 1000000000000) (37519345684 / 1000000000000), orderedInterval (28110517724 / 1000000000000) (28110517725 / 1000000000000))
    | 20 => (orderedInterval (-27369610209 / 1000000000000) (-27369607681 / 1000000000000), orderedInterval (52698417493 / 1000000000000) (52698420021 / 1000000000000))
    | 21 => (orderedInterval (-52672716832 / 1000000000000) (-52672716831 / 1000000000000), orderedInterval (-61109177312 / 1000000000000) (-61109177311 / 1000000000000))
    | 22 => (orderedInterval (44157061952 / 1000000000000) (44157061953 / 1000000000000), orderedInterval (21352662407 / 1000000000000) (21352662408 / 1000000000000))
    | 23 => (orderedInterval (-11699478156 / 1000000000000) (-11699478155 / 1000000000000), orderedInterval (-40328388511 / 1000000000000) (-40328388510 / 1000000000000))
    | 24 => (orderedInterval (36556730392 / 1000000000000) (36556740934 / 1000000000000), orderedInterval (-53380948221 / 1000000000000) (-53380937678 / 1000000000000))
    | 25 => (orderedInterval (-29045886823 / 1000000000000) (-29045802337 / 1000000000000), orderedInterval (13549426310 / 1000000000000) (13549510796 / 1000000000000))
    | _ => (orderedInterval (11700129861 / 1000000000000) (11700129862 / 1000000000000), orderedInterval (37403304157 / 1000000000000) (37403304158 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (19014112996 / 1000000000000) (19014119039 / 1000000000000)
      | 1 => orderedInterval (-4036211383 / 1000000000000) (-4036203888 / 1000000000000)
      | 2 => orderedInterval (-662623521 / 1000000000000) (-662623501 / 1000000000000)
      | 3 => orderedInterval (-1516749727 / 1000000000000) (-1516732731 / 1000000000000)
      | 4 => orderedInterval (3675585514 / 1000000000000) (3675585567 / 1000000000000)
      | 5 => orderedInterval (2248700711 / 1000000000000) (2248706487 / 1000000000000)
      | 6 => orderedInterval (-6518815370 / 1000000000000) (-6518814909 / 1000000000000)
      | 7 => orderedInterval (867457473 / 1000000000000) (867457514 / 1000000000000)
      | _ => orderedInterval (389501108 / 1000000000000) (389508142 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (3546463863 / 1000000000000) (3546471059 / 1000000000000)
      | 1 => orderedInterval (2270659188 / 1000000000000) (2270670908 / 1000000000000)
      | 2 => orderedInterval (-2424192673 / 1000000000000) (-2424192640 / 1000000000000)
      | 3 => orderedInterval (-8235852073 / 1000000000000) (-8235814088 / 1000000000000)
      | 4 => orderedInterval (1303754852 / 1000000000000) (1303754944 / 1000000000000)
      | 5 => orderedInterval (-1601582178 / 1000000000000) (-1601574762 / 1000000000000)
      | 6 => orderedInterval (5645069582 / 1000000000000) (5645070005 / 1000000000000)
      | 7 => orderedInterval (3289000931 / 1000000000000) (3289000967 / 1000000000000)
      | _ => orderedInterval (-10914247078 / 1000000000000) (-10914234130 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-19637817636 / 1000000000000) (-19637809046 / 1000000000000)
      | 1 => orderedInterval (5996314719 / 1000000000000) (5996333111 / 1000000000000)
      | 2 => orderedInterval (2772947346 / 1000000000000) (2772947404 / 1000000000000)
      | 3 => orderedInterval (977317558 / 1000000000000) (977402588 / 1000000000000)
      | 4 => orderedInterval (-9747089556 / 1000000000000) (-9747089390 / 1000000000000)
      | 5 => orderedInterval (-4934069193 / 1000000000000) (-4934059625 / 1000000000000)
      | 6 => orderedInterval (5508004609 / 1000000000000) (5508005016 / 1000000000000)
      | 7 => orderedInterval (-513160419 / 1000000000000) (-513160383 / 1000000000000)
      | _ => orderedInterval (-4801739721 / 1000000000000) (-4801715699 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-2825046715 / 1000000000000) (-2825036485 / 1000000000000)
      | 1 => orderedInterval (-4757486787 / 1000000000000) (-4757457965 / 1000000000000)
      | 2 => orderedInterval (7212727205 / 1000000000000) (7212727311 / 1000000000000)
      | 3 => orderedInterval (34309095523 / 1000000000000) (34309285639 / 1000000000000)
      | 4 => orderedInterval (-3056894174 / 1000000000000) (-3056893868 / 1000000000000)
      | 5 => orderedInterval (2792129958 / 1000000000000) (2792142319 / 1000000000000)
      | 6 => orderedInterval (-5628625924 / 1000000000000) (-5628625524 / 1000000000000)
      | 7 => orderedInterval (-3698467211 / 1000000000000) (-3698467174 / 1000000000000)
      | _ => orderedInterval (20581091466 / 1000000000000) (20581136052 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (20700691105 / 1000000000000) (20700703318 / 1000000000000)
      | 1 => orderedInterval (-13272043911 / 1000000000000) (-13271998648 / 1000000000000)
      | 2 => orderedInterval (-11234960661 / 1000000000000) (-11234960465 / 1000000000000)
      | 3 => orderedInterval (2493824149 / 1000000000000) (2494249834 / 1000000000000)
      | 4 => orderedInterval (28162344920 / 1000000000000) (28162345498 / 1000000000000)
      | 5 => orderedInterval (12647239088 / 1000000000000) (12647255176 / 1000000000000)
      | 6 => orderedInterval (-5079164094 / 1000000000000) (-5079163692 / 1000000000000)
      | 7 => orderedInterval (862507241 / 1000000000000) (862507280 / 1000000000000)
      | _ => orderedInterval (22925833095 / 1000000000000) (22925916047 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (13460957801 / 1000000000000) (13461001720 / 1000000000000)
    | 1 => orderedInterval (-7120925586 / 1000000000000) (-7120847737 / 1000000000000)
    | 2 => orderedInterval (-24379292293 / 1000000000000) (-24379146024 / 1000000000000)
    | 3 => orderedInterval (44928523341 / 1000000000000) (44928810305 / 1000000000000)
    | _ => orderedInterval (58206270932 / 1000000000000) (58206854348 / 1000000000000)

theorem compactCertificate462_stateChecks0 :
    compactCertificate462.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (667 / 2)) (orderedInterval (41808784683 / 1000000000000) (41808784685 / 1000000000000), orderedInterval (12623082147 / 1000000000000) (12623082150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (982618362249967 / 4000000000000)) (orderedInterval (50124611353 / 1000000000000) (50124611360 / 1000000000000), orderedInterval (8788552502 / 1000000000000) (8788552509 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (317758589183311 / 800000000000)) (orderedInterval (33665164371 / 1000000000000) (33665266934 / 1000000000000), orderedInterval (-21708728183 / 1000000000000) (-21708625620 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_stateChecks1 :
    compactCertificate462.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (286725587419469 / 4000000000000)) (orderedInterval (-19499472009 / 1000000000000) (-19499472008 / 1000000000000), orderedInterval (-92065994173 / 1000000000000) (-92065994172 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (770185259098793 / 4000000000000)) (orderedInterval (-57065283638 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546019 / 1000000000000) (7209546369 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2091202800822981 / 4000000000000)) (orderedInterval (30443341599 / 1000000000000) (30443446290 / 1000000000000), orderedInterval (-17085240242 / 1000000000000) (-17085135552 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_stateChecks2 :
    compactCertificate462.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1540370518198253 / 4000000000000)) (orderedInterval (20841241370 / 1000000000000) (20841242898 / 1000000000000), orderedInterval (-34938425546 / 1000000000000) (-34938424019 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2639451137707169 / 4000000000000)) (orderedInterval (24589901595 / 1000000000000) (24589901596 / 1000000000000), orderedInterval (18958002036 / 1000000000000) (18958002037 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1944207761747171 / 4000000000000)) (orderedInterval (3965050114 / 1000000000000) (3965050116 / 1000000000000), orderedInterval (-35977072879 / 1000000000000) (-35977072877 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_stateChecks3 :
    compactCertificate462.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2982914681984333 / 4000000000000)) (orderedInterval (-27072094947 / 1000000000000) (-27072000275 / 1000000000000), orderedInterval (11008655864 / 1000000000000) (11008750536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1722186594613157 / 4000000000000)) (orderedInterval (-30906372759 / 1000000000000) (-30906372758 / 1000000000000), orderedInterval (-22842639060 / 1000000000000) (-22842639059 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3056050333628713 / 4000000000000)) (orderedInterval (-28399873494 / 1000000000000) (-28399873201 / 1000000000000), orderedInterval (-5149126985 / 1000000000000) (-5149126692 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_stateChecks4 :
    compactCertificate462.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2855358642098797 / 4000000000000)) (orderedInterval (-29749324398 / 1000000000000) (-29749323715 / 1000000000000), orderedInterval (-2587247546 / 1000000000000) (-2587246863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2037718659023101 / 4000000000000)) (orderedInterval (33833988836 / 1000000000000) (33833988844 / 1000000000000), orderedInterval (10210437907 / 1000000000000) (10210437916 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2310555777296379 / 4000000000000)) (orderedInterval (12038257652 / 1000000000000) (12038257653 / 1000000000000), orderedInterval (30928025030 / 1000000000000) (30928025031 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_stateChecks5 :
    compactCertificate462.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1926300519560651 / 4000000000000)) (orderedInterval (-36071362386 / 1000000000000) (-36071360291 / 1000000000000), orderedInterval (4599179686 / 1000000000000) (4599181781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1701944927865671 / 4000000000000)) (orderedInterval (-32237461672 / 1000000000000) (-32237362868 / 1000000000000), orderedInterval (21414591827 / 1000000000000) (21414690631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (493289976585429 / 800000000000)) (orderedInterval (32042078051 / 1000000000000) (32042080593 / 1000000000000), orderedInterval (-2424303703 / 1000000000000) (-2424301161 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_stateChecks6 :
    compactCertificate462.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1364466035664463 / 4000000000000)) (orderedInterval (21915961740 / 1000000000000) (21915963577 / 1000000000000), orderedInterval (-37260797194 / 1000000000000) (-37260795358 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1156672969480343 / 4000000000000)) (orderedInterval (37519345683 / 1000000000000) (37519345684 / 1000000000000), orderedInterval (28110517724 / 1000000000000) (28110517725 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (723792238252829 / 4000000000000)) (orderedInterval (-27369610209 / 1000000000000) (-27369607681 / 1000000000000), orderedInterval (52698417493 / 1000000000000) (52698420021 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_stateChecks7 :
    compactCertificate462.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (389257872956643 / 4000000000000)) (orderedInterval (-52672716832 / 1000000000000) (-52672716831 / 1000000000000), orderedInterval (-61109177312 / 1000000000000) (-61109177311 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1056910846518929 / 4000000000000)) (orderedInterval (44157061952 / 1000000000000) (44157061953 / 1000000000000), orderedInterval (21352662407 / 1000000000000) (21352662408 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1443121402834033 / 4000000000000)) (orderedInterval (-11699478156 / 1000000000000) (-11699478155 / 1000000000000), orderedInterval (-40328388511 / 1000000000000) (-40328388510 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_stateChecks8 :
    compactCertificate462.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (610207761747171 / 4000000000000)) (orderedInterval (36556730392 / 1000000000000) (36556740934 / 1000000000000), orderedInterval (-53380948221 / 1000000000000) (-53380937678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2480460673780291 / 4000000000000)) (orderedInterval (-29045886823 / 1000000000000) (-29045802337 / 1000000000000), orderedInterval (13549426310 / 1000000000000) (13549510796 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1656832775457869 / 4000000000000)) (orderedInterval (11700129861 / 1000000000000) (11700129862 / 1000000000000), orderedInterval (37403304157 / 1000000000000) (37403304158 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_states : ∀ j,
    BesselStateValid (compactCertificate462.point j) (compactCertificate462.state j) :=
  compactCertificate462.statesValid_of_checks3 compactCertificate462_stateChecks0
    compactCertificate462_stateChecks1 compactCertificate462_stateChecks2
    compactCertificate462_stateChecks3 compactCertificate462_stateChecks4
    compactCertificate462_stateChecks5 compactCertificate462_stateChecks6
    compactCertificate462_stateChecks7 compactCertificate462_stateChecks8

theorem compactCertificate462_chunkChecks0_0 :
    compactCertificate462.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (667 / 2) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41808784683 / 1000000000000) (41808784685 / 1000000000000), orderedInterval (12623082147 / 1000000000000) (12623082150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (982618362249967 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50124611353 / 1000000000000) (50124611360 / 1000000000000), orderedInterval (8788552502 / 1000000000000) (8788552509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (317758589183311 / 800000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33665164371 / 1000000000000) (33665266934 / 1000000000000), orderedInterval (-21708728183 / 1000000000000) (-21708625620 / 1000000000000)))) (orderedInterval (19014112996 / 1000000000000) (19014119039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (286725587419469 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19499472009 / 1000000000000) (-19499472008 / 1000000000000), orderedInterval (-92065994173 / 1000000000000) (-92065994172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (770185259098793 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57065283638 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546019 / 1000000000000) (7209546369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2091202800822981 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30443341599 / 1000000000000) (30443446290 / 1000000000000), orderedInterval (-17085240242 / 1000000000000) (-17085135552 / 1000000000000)))) (orderedInterval (-4036211383 / 1000000000000) (-4036203888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1540370518198253 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20841241370 / 1000000000000) (20841242898 / 1000000000000), orderedInterval (-34938425546 / 1000000000000) (-34938424019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2639451137707169 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24589901595 / 1000000000000) (24589901596 / 1000000000000), orderedInterval (18958002036 / 1000000000000) (18958002037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1944207761747171 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3965050114 / 1000000000000) (3965050116 / 1000000000000), orderedInterval (-35977072879 / 1000000000000) (-35977072877 / 1000000000000)))) (orderedInterval (-662623521 / 1000000000000) (-662623501 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks0_1 :
    compactCertificate462.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2982914681984333 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27072094947 / 1000000000000) (-27072000275 / 1000000000000), orderedInterval (11008655864 / 1000000000000) (11008750536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1722186594613157 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30906372759 / 1000000000000) (-30906372758 / 1000000000000), orderedInterval (-22842639060 / 1000000000000) (-22842639059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3056050333628713 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28399873494 / 1000000000000) (-28399873201 / 1000000000000), orderedInterval (-5149126985 / 1000000000000) (-5149126692 / 1000000000000)))) (orderedInterval (-1516749727 / 1000000000000) (-1516732731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2855358642098797 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29749324398 / 1000000000000) (-29749323715 / 1000000000000), orderedInterval (-2587247546 / 1000000000000) (-2587246863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2037718659023101 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33833988836 / 1000000000000) (33833988844 / 1000000000000), orderedInterval (10210437907 / 1000000000000) (10210437916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2310555777296379 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12038257652 / 1000000000000) (12038257653 / 1000000000000), orderedInterval (30928025030 / 1000000000000) (30928025031 / 1000000000000)))) (orderedInterval (3675585514 / 1000000000000) (3675585567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1926300519560651 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36071362386 / 1000000000000) (-36071360291 / 1000000000000), orderedInterval (4599179686 / 1000000000000) (4599181781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1701944927865671 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32237461672 / 1000000000000) (-32237362868 / 1000000000000), orderedInterval (21414591827 / 1000000000000) (21414690631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (493289976585429 / 800000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32042078051 / 1000000000000) (32042080593 / 1000000000000), orderedInterval (-2424303703 / 1000000000000) (-2424301161 / 1000000000000)))) (orderedInterval (2248700711 / 1000000000000) (2248706487 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks0_2 :
    compactCertificate462.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1364466035664463 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21915961740 / 1000000000000) (21915963577 / 1000000000000), orderedInterval (-37260797194 / 1000000000000) (-37260795358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1156672969480343 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37519345683 / 1000000000000) (37519345684 / 1000000000000), orderedInterval (28110517724 / 1000000000000) (28110517725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (723792238252829 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27369610209 / 1000000000000) (-27369607681 / 1000000000000), orderedInterval (52698417493 / 1000000000000) (52698420021 / 1000000000000)))) (orderedInterval (-6518815370 / 1000000000000) (-6518814909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (389257872956643 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52672716832 / 1000000000000) (-52672716831 / 1000000000000), orderedInterval (-61109177312 / 1000000000000) (-61109177311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1056910846518929 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44157061952 / 1000000000000) (44157061953 / 1000000000000), orderedInterval (21352662407 / 1000000000000) (21352662408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1443121402834033 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11699478156 / 1000000000000) (-11699478155 / 1000000000000), orderedInterval (-40328388511 / 1000000000000) (-40328388510 / 1000000000000)))) (orderedInterval (867457473 / 1000000000000) (867457514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (610207761747171 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36556730392 / 1000000000000) (36556740934 / 1000000000000), orderedInterval (-53380948221 / 1000000000000) (-53380937678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2480460673780291 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29045886823 / 1000000000000) (-29045802337 / 1000000000000), orderedInterval (13549426310 / 1000000000000) (13549510796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1656832775457869 / 4000000000000) 0 (IntervalRat.scale (667 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11700129861 / 1000000000000) (11700129862 / 1000000000000), orderedInterval (37403304157 / 1000000000000) (37403304158 / 1000000000000)))) (orderedInterval (389501108 / 1000000000000) (389508142 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks0 :
    compactCertificate462.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate462.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate462_chunkChecks0_0
    compactCertificate462_chunkChecks0_1 compactCertificate462_chunkChecks0_2

theorem compactCertificate462_chunkChecks1_0 :
    compactCertificate462.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (667 / 2) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41808784683 / 1000000000000) (41808784685 / 1000000000000), orderedInterval (12623082147 / 1000000000000) (12623082150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (982618362249967 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50124611353 / 1000000000000) (50124611360 / 1000000000000), orderedInterval (8788552502 / 1000000000000) (8788552509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (317758589183311 / 800000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33665164371 / 1000000000000) (33665266934 / 1000000000000), orderedInterval (-21708728183 / 1000000000000) (-21708625620 / 1000000000000)))) (orderedInterval (3546463863 / 1000000000000) (3546471059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (286725587419469 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19499472009 / 1000000000000) (-19499472008 / 1000000000000), orderedInterval (-92065994173 / 1000000000000) (-92065994172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (770185259098793 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57065283638 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546019 / 1000000000000) (7209546369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2091202800822981 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30443341599 / 1000000000000) (30443446290 / 1000000000000), orderedInterval (-17085240242 / 1000000000000) (-17085135552 / 1000000000000)))) (orderedInterval (2270659188 / 1000000000000) (2270670908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1540370518198253 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20841241370 / 1000000000000) (20841242898 / 1000000000000), orderedInterval (-34938425546 / 1000000000000) (-34938424019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2639451137707169 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24589901595 / 1000000000000) (24589901596 / 1000000000000), orderedInterval (18958002036 / 1000000000000) (18958002037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1944207761747171 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3965050114 / 1000000000000) (3965050116 / 1000000000000), orderedInterval (-35977072879 / 1000000000000) (-35977072877 / 1000000000000)))) (orderedInterval (-2424192673 / 1000000000000) (-2424192640 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks1_1 :
    compactCertificate462.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2982914681984333 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27072094947 / 1000000000000) (-27072000275 / 1000000000000), orderedInterval (11008655864 / 1000000000000) (11008750536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1722186594613157 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30906372759 / 1000000000000) (-30906372758 / 1000000000000), orderedInterval (-22842639060 / 1000000000000) (-22842639059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3056050333628713 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28399873494 / 1000000000000) (-28399873201 / 1000000000000), orderedInterval (-5149126985 / 1000000000000) (-5149126692 / 1000000000000)))) (orderedInterval (-8235852073 / 1000000000000) (-8235814088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2855358642098797 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29749324398 / 1000000000000) (-29749323715 / 1000000000000), orderedInterval (-2587247546 / 1000000000000) (-2587246863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2037718659023101 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33833988836 / 1000000000000) (33833988844 / 1000000000000), orderedInterval (10210437907 / 1000000000000) (10210437916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2310555777296379 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12038257652 / 1000000000000) (12038257653 / 1000000000000), orderedInterval (30928025030 / 1000000000000) (30928025031 / 1000000000000)))) (orderedInterval (1303754852 / 1000000000000) (1303754944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1926300519560651 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36071362386 / 1000000000000) (-36071360291 / 1000000000000), orderedInterval (4599179686 / 1000000000000) (4599181781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1701944927865671 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32237461672 / 1000000000000) (-32237362868 / 1000000000000), orderedInterval (21414591827 / 1000000000000) (21414690631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (493289976585429 / 800000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32042078051 / 1000000000000) (32042080593 / 1000000000000), orderedInterval (-2424303703 / 1000000000000) (-2424301161 / 1000000000000)))) (orderedInterval (-1601582178 / 1000000000000) (-1601574762 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks1_2 :
    compactCertificate462.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1364466035664463 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21915961740 / 1000000000000) (21915963577 / 1000000000000), orderedInterval (-37260797194 / 1000000000000) (-37260795358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1156672969480343 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37519345683 / 1000000000000) (37519345684 / 1000000000000), orderedInterval (28110517724 / 1000000000000) (28110517725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (723792238252829 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27369610209 / 1000000000000) (-27369607681 / 1000000000000), orderedInterval (52698417493 / 1000000000000) (52698420021 / 1000000000000)))) (orderedInterval (5645069582 / 1000000000000) (5645070005 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (389257872956643 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52672716832 / 1000000000000) (-52672716831 / 1000000000000), orderedInterval (-61109177312 / 1000000000000) (-61109177311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1056910846518929 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44157061952 / 1000000000000) (44157061953 / 1000000000000), orderedInterval (21352662407 / 1000000000000) (21352662408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1443121402834033 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11699478156 / 1000000000000) (-11699478155 / 1000000000000), orderedInterval (-40328388511 / 1000000000000) (-40328388510 / 1000000000000)))) (orderedInterval (3289000931 / 1000000000000) (3289000967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (610207761747171 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36556730392 / 1000000000000) (36556740934 / 1000000000000), orderedInterval (-53380948221 / 1000000000000) (-53380937678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2480460673780291 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29045886823 / 1000000000000) (-29045802337 / 1000000000000), orderedInterval (13549426310 / 1000000000000) (13549510796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1656832775457869 / 4000000000000) 1 (IntervalRat.scale (667 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11700129861 / 1000000000000) (11700129862 / 1000000000000), orderedInterval (37403304157 / 1000000000000) (37403304158 / 1000000000000)))) (orderedInterval (-10914247078 / 1000000000000) (-10914234130 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks1 :
    compactCertificate462.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate462.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate462_chunkChecks1_0
    compactCertificate462_chunkChecks1_1 compactCertificate462_chunkChecks1_2

theorem compactCertificate462_chunkChecks2_0 :
    compactCertificate462.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (667 / 2) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41808784683 / 1000000000000) (41808784685 / 1000000000000), orderedInterval (12623082147 / 1000000000000) (12623082150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (982618362249967 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50124611353 / 1000000000000) (50124611360 / 1000000000000), orderedInterval (8788552502 / 1000000000000) (8788552509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (317758589183311 / 800000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33665164371 / 1000000000000) (33665266934 / 1000000000000), orderedInterval (-21708728183 / 1000000000000) (-21708625620 / 1000000000000)))) (orderedInterval (-19637817636 / 1000000000000) (-19637809046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (286725587419469 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19499472009 / 1000000000000) (-19499472008 / 1000000000000), orderedInterval (-92065994173 / 1000000000000) (-92065994172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (770185259098793 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57065283638 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546019 / 1000000000000) (7209546369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2091202800822981 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30443341599 / 1000000000000) (30443446290 / 1000000000000), orderedInterval (-17085240242 / 1000000000000) (-17085135552 / 1000000000000)))) (orderedInterval (5996314719 / 1000000000000) (5996333111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1540370518198253 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20841241370 / 1000000000000) (20841242898 / 1000000000000), orderedInterval (-34938425546 / 1000000000000) (-34938424019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2639451137707169 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24589901595 / 1000000000000) (24589901596 / 1000000000000), orderedInterval (18958002036 / 1000000000000) (18958002037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1944207761747171 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3965050114 / 1000000000000) (3965050116 / 1000000000000), orderedInterval (-35977072879 / 1000000000000) (-35977072877 / 1000000000000)))) (orderedInterval (2772947346 / 1000000000000) (2772947404 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks2_1 :
    compactCertificate462.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2982914681984333 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27072094947 / 1000000000000) (-27072000275 / 1000000000000), orderedInterval (11008655864 / 1000000000000) (11008750536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1722186594613157 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30906372759 / 1000000000000) (-30906372758 / 1000000000000), orderedInterval (-22842639060 / 1000000000000) (-22842639059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3056050333628713 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28399873494 / 1000000000000) (-28399873201 / 1000000000000), orderedInterval (-5149126985 / 1000000000000) (-5149126692 / 1000000000000)))) (orderedInterval (977317558 / 1000000000000) (977402588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2855358642098797 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29749324398 / 1000000000000) (-29749323715 / 1000000000000), orderedInterval (-2587247546 / 1000000000000) (-2587246863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2037718659023101 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33833988836 / 1000000000000) (33833988844 / 1000000000000), orderedInterval (10210437907 / 1000000000000) (10210437916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2310555777296379 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12038257652 / 1000000000000) (12038257653 / 1000000000000), orderedInterval (30928025030 / 1000000000000) (30928025031 / 1000000000000)))) (orderedInterval (-9747089556 / 1000000000000) (-9747089390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1926300519560651 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36071362386 / 1000000000000) (-36071360291 / 1000000000000), orderedInterval (4599179686 / 1000000000000) (4599181781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1701944927865671 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32237461672 / 1000000000000) (-32237362868 / 1000000000000), orderedInterval (21414591827 / 1000000000000) (21414690631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (493289976585429 / 800000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32042078051 / 1000000000000) (32042080593 / 1000000000000), orderedInterval (-2424303703 / 1000000000000) (-2424301161 / 1000000000000)))) (orderedInterval (-4934069193 / 1000000000000) (-4934059625 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks2_2 :
    compactCertificate462.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1364466035664463 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21915961740 / 1000000000000) (21915963577 / 1000000000000), orderedInterval (-37260797194 / 1000000000000) (-37260795358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1156672969480343 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37519345683 / 1000000000000) (37519345684 / 1000000000000), orderedInterval (28110517724 / 1000000000000) (28110517725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (723792238252829 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27369610209 / 1000000000000) (-27369607681 / 1000000000000), orderedInterval (52698417493 / 1000000000000) (52698420021 / 1000000000000)))) (orderedInterval (5508004609 / 1000000000000) (5508005016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (389257872956643 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52672716832 / 1000000000000) (-52672716831 / 1000000000000), orderedInterval (-61109177312 / 1000000000000) (-61109177311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1056910846518929 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44157061952 / 1000000000000) (44157061953 / 1000000000000), orderedInterval (21352662407 / 1000000000000) (21352662408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1443121402834033 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11699478156 / 1000000000000) (-11699478155 / 1000000000000), orderedInterval (-40328388511 / 1000000000000) (-40328388510 / 1000000000000)))) (orderedInterval (-513160419 / 1000000000000) (-513160383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (610207761747171 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36556730392 / 1000000000000) (36556740934 / 1000000000000), orderedInterval (-53380948221 / 1000000000000) (-53380937678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2480460673780291 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29045886823 / 1000000000000) (-29045802337 / 1000000000000), orderedInterval (13549426310 / 1000000000000) (13549510796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1656832775457869 / 4000000000000) 2 (IntervalRat.scale (667 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11700129861 / 1000000000000) (11700129862 / 1000000000000), orderedInterval (37403304157 / 1000000000000) (37403304158 / 1000000000000)))) (orderedInterval (-4801739721 / 1000000000000) (-4801715699 / 1000000000000))) = true
  rfl'

theorem compactCertificate462_chunkChecks2 :
    compactCertificate462.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate462.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate462_chunkChecks2_0
    compactCertificate462_chunkChecks2_1 compactCertificate462_chunkChecks2_2

theorem compactCertificate462_chunkChecks3_0 :
    compactCertificate462.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (667 / 2) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41808784683 / 1000000000000) (41808784685 / 1000000000000), orderedInterval (12623082147 / 1000000000000) (12623082150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (982618362249967 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50124611353 / 1000000000000) (50124611360 / 1000000000000), orderedInterval (8788552502 / 1000000000000) (8788552509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (317758589183311 / 800000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33665164371 / 1000000000000) (33665266934 / 1000000000000), orderedInterval (-21708728183 / 1000000000000) (-21708625620 / 1000000000000)))) (orderedInterval (-2825046715 / 1000000000000) (-2825036485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (286725587419469 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19499472009 / 1000000000000) (-19499472008 / 1000000000000), orderedInterval (-92065994173 / 1000000000000) (-92065994172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (770185259098793 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57065283638 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546019 / 1000000000000) (7209546369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2091202800822981 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30443341599 / 1000000000000) (30443446290 / 1000000000000), orderedInterval (-17085240242 / 1000000000000) (-17085135552 / 1000000000000)))) (orderedInterval (-4757486787 / 1000000000000) (-4757457965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1540370518198253 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20841241370 / 1000000000000) (20841242898 / 1000000000000), orderedInterval (-34938425546 / 1000000000000) (-34938424019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2639451137707169 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24589901595 / 1000000000000) (24589901596 / 1000000000000), orderedInterval (18958002036 / 1000000000000) (18958002037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1944207761747171 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3965050114 / 1000000000000) (3965050116 / 1000000000000), orderedInterval (-35977072879 / 1000000000000) (-35977072877 / 1000000000000)))) (orderedInterval (7212727205 / 1000000000000) (7212727311 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate462_chunkChecks3_1 :
    compactCertificate462.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2982914681984333 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27072094947 / 1000000000000) (-27072000275 / 1000000000000), orderedInterval (11008655864 / 1000000000000) (11008750536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1722186594613157 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30906372759 / 1000000000000) (-30906372758 / 1000000000000), orderedInterval (-22842639060 / 1000000000000) (-22842639059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3056050333628713 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28399873494 / 1000000000000) (-28399873201 / 1000000000000), orderedInterval (-5149126985 / 1000000000000) (-5149126692 / 1000000000000)))) (orderedInterval (34309095523 / 1000000000000) (34309285639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2855358642098797 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29749324398 / 1000000000000) (-29749323715 / 1000000000000), orderedInterval (-2587247546 / 1000000000000) (-2587246863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2037718659023101 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33833988836 / 1000000000000) (33833988844 / 1000000000000), orderedInterval (10210437907 / 1000000000000) (10210437916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2310555777296379 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12038257652 / 1000000000000) (12038257653 / 1000000000000), orderedInterval (30928025030 / 1000000000000) (30928025031 / 1000000000000)))) (orderedInterval (-3056894174 / 1000000000000) (-3056893868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1926300519560651 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36071362386 / 1000000000000) (-36071360291 / 1000000000000), orderedInterval (4599179686 / 1000000000000) (4599181781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1701944927865671 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32237461672 / 1000000000000) (-32237362868 / 1000000000000), orderedInterval (21414591827 / 1000000000000) (21414690631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (493289976585429 / 800000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32042078051 / 1000000000000) (32042080593 / 1000000000000), orderedInterval (-2424303703 / 1000000000000) (-2424301161 / 1000000000000)))) (orderedInterval (2792129958 / 1000000000000) (2792142319 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate462_chunkChecks3_2 :
    compactCertificate462.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1364466035664463 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21915961740 / 1000000000000) (21915963577 / 1000000000000), orderedInterval (-37260797194 / 1000000000000) (-37260795358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1156672969480343 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37519345683 / 1000000000000) (37519345684 / 1000000000000), orderedInterval (28110517724 / 1000000000000) (28110517725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (723792238252829 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27369610209 / 1000000000000) (-27369607681 / 1000000000000), orderedInterval (52698417493 / 1000000000000) (52698420021 / 1000000000000)))) (orderedInterval (-5628625924 / 1000000000000) (-5628625524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (389257872956643 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52672716832 / 1000000000000) (-52672716831 / 1000000000000), orderedInterval (-61109177312 / 1000000000000) (-61109177311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1056910846518929 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44157061952 / 1000000000000) (44157061953 / 1000000000000), orderedInterval (21352662407 / 1000000000000) (21352662408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1443121402834033 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11699478156 / 1000000000000) (-11699478155 / 1000000000000), orderedInterval (-40328388511 / 1000000000000) (-40328388510 / 1000000000000)))) (orderedInterval (-3698467211 / 1000000000000) (-3698467174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (610207761747171 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36556730392 / 1000000000000) (36556740934 / 1000000000000), orderedInterval (-53380948221 / 1000000000000) (-53380937678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2480460673780291 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29045886823 / 1000000000000) (-29045802337 / 1000000000000), orderedInterval (13549426310 / 1000000000000) (13549510796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1656832775457869 / 4000000000000) 3 (IntervalRat.scale (667 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11700129861 / 1000000000000) (11700129862 / 1000000000000), orderedInterval (37403304157 / 1000000000000) (37403304158 / 1000000000000)))) (orderedInterval (20581091466 / 1000000000000) (20581136052 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate462_chunkChecks3 :
    compactCertificate462.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate462.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate462_chunkChecks3_0
    compactCertificate462_chunkChecks3_1 compactCertificate462_chunkChecks3_2

theorem compactCertificate462_chunkChecks4_0 :
    compactCertificate462.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (667 / 2) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41808784683 / 1000000000000) (41808784685 / 1000000000000), orderedInterval (12623082147 / 1000000000000) (12623082150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (982618362249967 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (50124611353 / 1000000000000) (50124611360 / 1000000000000), orderedInterval (8788552502 / 1000000000000) (8788552509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (317758589183311 / 800000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33665164371 / 1000000000000) (33665266934 / 1000000000000), orderedInterval (-21708728183 / 1000000000000) (-21708625620 / 1000000000000)))) (orderedInterval (20700691105 / 1000000000000) (20700703318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (286725587419469 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19499472009 / 1000000000000) (-19499472008 / 1000000000000), orderedInterval (-92065994173 / 1000000000000) (-92065994172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (770185259098793 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57065283638 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546019 / 1000000000000) (7209546369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2091202800822981 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30443341599 / 1000000000000) (30443446290 / 1000000000000), orderedInterval (-17085240242 / 1000000000000) (-17085135552 / 1000000000000)))) (orderedInterval (-13272043911 / 1000000000000) (-13271998648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1540370518198253 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (20841241370 / 1000000000000) (20841242898 / 1000000000000), orderedInterval (-34938425546 / 1000000000000) (-34938424019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2639451137707169 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24589901595 / 1000000000000) (24589901596 / 1000000000000), orderedInterval (18958002036 / 1000000000000) (18958002037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1944207761747171 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3965050114 / 1000000000000) (3965050116 / 1000000000000), orderedInterval (-35977072879 / 1000000000000) (-35977072877 / 1000000000000)))) (orderedInterval (-11234960661 / 1000000000000) (-11234960465 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate462_chunkChecks4_1 :
    compactCertificate462.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2982914681984333 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27072094947 / 1000000000000) (-27072000275 / 1000000000000), orderedInterval (11008655864 / 1000000000000) (11008750536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1722186594613157 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30906372759 / 1000000000000) (-30906372758 / 1000000000000), orderedInterval (-22842639060 / 1000000000000) (-22842639059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3056050333628713 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28399873494 / 1000000000000) (-28399873201 / 1000000000000), orderedInterval (-5149126985 / 1000000000000) (-5149126692 / 1000000000000)))) (orderedInterval (2493824149 / 1000000000000) (2494249834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2855358642098797 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29749324398 / 1000000000000) (-29749323715 / 1000000000000), orderedInterval (-2587247546 / 1000000000000) (-2587246863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2037718659023101 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33833988836 / 1000000000000) (33833988844 / 1000000000000), orderedInterval (10210437907 / 1000000000000) (10210437916 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2310555777296379 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12038257652 / 1000000000000) (12038257653 / 1000000000000), orderedInterval (30928025030 / 1000000000000) (30928025031 / 1000000000000)))) (orderedInterval (28162344920 / 1000000000000) (28162345498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1926300519560651 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36071362386 / 1000000000000) (-36071360291 / 1000000000000), orderedInterval (4599179686 / 1000000000000) (4599181781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1701944927865671 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32237461672 / 1000000000000) (-32237362868 / 1000000000000), orderedInterval (21414591827 / 1000000000000) (21414690631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (493289976585429 / 800000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32042078051 / 1000000000000) (32042080593 / 1000000000000), orderedInterval (-2424303703 / 1000000000000) (-2424301161 / 1000000000000)))) (orderedInterval (12647239088 / 1000000000000) (12647255176 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate462_chunkChecks4_2 :
    compactCertificate462.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1364466035664463 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21915961740 / 1000000000000) (21915963577 / 1000000000000), orderedInterval (-37260797194 / 1000000000000) (-37260795358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1156672969480343 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37519345683 / 1000000000000) (37519345684 / 1000000000000), orderedInterval (28110517724 / 1000000000000) (28110517725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (723792238252829 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27369610209 / 1000000000000) (-27369607681 / 1000000000000), orderedInterval (52698417493 / 1000000000000) (52698420021 / 1000000000000)))) (orderedInterval (-5079164094 / 1000000000000) (-5079163692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (389257872956643 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52672716832 / 1000000000000) (-52672716831 / 1000000000000), orderedInterval (-61109177312 / 1000000000000) (-61109177311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1056910846518929 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44157061952 / 1000000000000) (44157061953 / 1000000000000), orderedInterval (21352662407 / 1000000000000) (21352662408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1443121402834033 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11699478156 / 1000000000000) (-11699478155 / 1000000000000), orderedInterval (-40328388511 / 1000000000000) (-40328388510 / 1000000000000)))) (orderedInterval (862507241 / 1000000000000) (862507280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (610207761747171 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36556730392 / 1000000000000) (36556740934 / 1000000000000), orderedInterval (-53380948221 / 1000000000000) (-53380937678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2480460673780291 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29045886823 / 1000000000000) (-29045802337 / 1000000000000), orderedInterval (13549426310 / 1000000000000) (13549510796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1656832775457869 / 4000000000000) 4 (IntervalRat.scale (667 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11700129861 / 1000000000000) (11700129862 / 1000000000000), orderedInterval (37403304157 / 1000000000000) (37403304158 / 1000000000000)))) (orderedInterval (22925833095 / 1000000000000) (22925916047 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate462_chunkChecks4 :
    compactCertificate462.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate462.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate462_chunkChecks4_0
    compactCertificate462_chunkChecks4_1 compactCertificate462_chunkChecks4_2

theorem compactCertificate462_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate462.chunkCheck r b = true :=
  compactCertificate462.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate462_chunkChecks0
    · exact compactCertificate462_chunkChecks1
    · exact compactCertificate462_chunkChecks2
    · exact compactCertificate462_chunkChecks3
    · exact compactCertificate462_chunkChecks4)

theorem compactCertificate462_coefficient0 :
    compactCertificate462.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate462_coefficient1 :
    compactCertificate462.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate462_coefficient2 :
    compactCertificate462.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate462_coefficient3 :
    compactCertificate462.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate462_coefficient4 :
    compactCertificate462.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate462_coefficients : ∀ r : Fin 5,
    compactCertificate462.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate462_coefficient0
  · exact compactCertificate462_coefficient1
  · exact compactCertificate462_coefficient2
  · exact compactCertificate462_coefficient3
  · exact compactCertificate462_coefficient4

theorem compactCertificate462_lower : (1 : ℚ) ≤ compactCertificate462.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate462, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate462_proves {t : ℝ} (ht : t ∈ compactCertificate462.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate462.proves compactCertificate462_states compactCertificate462_chunks
    compactCertificate462_coefficients compactCertificate462_lower ht

end Erdos232
