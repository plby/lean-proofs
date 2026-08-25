/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate569 : CompactCertificate where
  left := 440
  right := 441
  center := 881 / 2
  grid := fun i =>
    match i.val with
    | 0 => 140
    | 1 => 103
    | 2 => 167
    | 3 => 30
    | 4 => 81
    | 5 => 220
    | 6 => 162
    | 7 => 278
    | 8 => 204
    | 9 => 314
    | 10 => 181
    | 11 => 321
    | 12 => 300
    | 13 => 214
    | 14 => 243
    | 15 => 203
    | 16 => 179
    | 17 => 259
    | 18 => 143
    | 19 => 122
    | 20 => 76
    | 21 => 41
    | 22 => 111
    | 23 => 152
    | 24 => 64
    | 25 => 261
    | _ => 174
  point := fun i =>
    match i.val with
    | 0 => 881 / 2
    | 1 => 1297881225100781 / 4000000000000
    | 2 => 419708121544973 / 800000000000
    | 3 => 378718504522567 / 4000000000000
    | 4 => 1017291174311899 / 4000000000000
    | 5 => 2762143429572783 / 4000000000000
    | 6 => 2034582348624679 / 4000000000000
    | 7 => 3486291532713667 / 4000000000000
    | 8 => 2567986563866953 / 4000000000000
    | 9 => 3939951776354119 / 4000000000000
    | 10 => 2274732218671951 / 4000000000000
    | 11 => 4036552239770459 / 4000000000000
    | 12 => 3771470710178471 / 4000000000000
    | 13 => 2691499458169943 / 4000000000000
    | 14 => 3051873522935697 / 4000000000000
    | 15 => 2544333969614593 / 4000000000000
    | 16 => 2247996224062453 / 4000000000000
    | 17 => 651556925594847 / 800000000000
    | 18 => 1802240745757709 / 4000000000000
    | 19 => 1527779439448549 / 4000000000000
    | 20 => 956013436133047 / 4000000000000
    | 21 => 514147205509449 / 4000000000000
    | 22 => 1396009678835347 / 4000000000000
    | 23 => 1906131867911219 / 4000000000000
    | 24 => 805986563866953 / 4000000000000
    | 25 => 3276290635083113 / 4000000000000
    | _ => 2188410307613767 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (37791867921 / 1000000000000) (37791868004 / 1000000000000), orderedInterval (4079557741 / 1000000000000) (4079557824 / 1000000000000))
    | 1 => (orderedInterval (-44071342404 / 1000000000000) (-44071341795 / 1000000000000), orderedInterval (4511149443 / 1000000000000) (4511150052 / 1000000000000))
    | 2 => (orderedInterval (-24357891183 / 1000000000000) (-24357891182 / 1000000000000), orderedInterval (-24879507169 / 1000000000000) (-24879507168 / 1000000000000))
    | 3 => (orderedInterval (76889764936 / 1000000000000) (76889764937 / 1000000000000), orderedInterval (28086575818 / 1000000000000) (28086575819 / 1000000000000))
    | 4 => (orderedInterval (-29826439441 / 1000000000000) (-29826439440 / 1000000000000), orderedInterval (-40110762603 / 1000000000000) (-40110762602 / 1000000000000))
    | 5 => (orderedInterval (5157579506 / 1000000000000) (5157579507 / 1000000000000), orderedInterval (29918180302 / 1000000000000) (29918180303 / 1000000000000))
    | 6 => (orderedInterval (16734911158 / 1000000000000) (16734911159 / 1000000000000), orderedInterval (31153102470 / 1000000000000) (31153102471 / 1000000000000))
    | 7 => (orderedInterval (-22809154410 / 1000000000000) (-22809138956 / 1000000000000), orderedInterval (14510286855 / 1000000000000) (14510302310 / 1000000000000))
    | 8 => (orderedInterval (29830018418 / 1000000000000) (29830054087 / 1000000000000), orderedInterval (-10112523344 / 1000000000000) (-10112487676 / 1000000000000))
    | 9 => (orderedInterval (-16121307050 / 1000000000000) (-16121306826 / 1000000000000), orderedInterval (19665901447 / 1000000000000) (19665901670 / 1000000000000))
    | 10 => (orderedInterval (-24913715709 / 1000000000000) (-24913715708 / 1000000000000), orderedInterval (-22311253534 / 1000000000000) (-22311253533 / 1000000000000))
    | 11 => (orderedInterval (-24994576259 / 1000000000000) (-24994572893 / 1000000000000), orderedInterval (-2462722750 / 1000000000000) (-2462719384 / 1000000000000))
    | 12 => (orderedInterval (23977123215 / 1000000000000) (23977123267 / 1000000000000), orderedInterval (10001911239 / 1000000000000) (10001911291 / 1000000000000))
    | 13 => (orderedInterval (30073339888 / 1000000000000) (30073339990 / 1000000000000), orderedInterval (6436221259 / 1000000000000) (6436221361 / 1000000000000))
    | 14 => (orderedInterval (-9812622543 / 1000000000000) (-9812622542 / 1000000000000), orderedInterval (-27161771589 / 1000000000000) (-27161771588 / 1000000000000))
    | 15 => (orderedInterval (24274258729 / 1000000000000) (24274272674 / 1000000000000), orderedInterval (-20307090694 / 1000000000000) (-20307076749 / 1000000000000))
    | 16 => (orderedInterval (-14309751249 / 1000000000000) (-14309751248 / 1000000000000), orderedInterval (-30450502534 / 1000000000000) (-30450502533 / 1000000000000))
    | 17 => (orderedInterval (-27956200369 / 1000000000000) (-27956197413 / 1000000000000), orderedInterval (-315307638 / 1000000000000) (-315304682 / 1000000000000))
    | 18 => (orderedInterval (-32493675105 / 1000000000000) (-32493586958 / 1000000000000), orderedInterval (18933503474 / 1000000000000) (18933591621 / 1000000000000))
    | 19 => (orderedInterval (-21143175473 / 1000000000000) (-21143173803 / 1000000000000), orderedInterval (34952615881 / 1000000000000) (34952617551 / 1000000000000))
    | 20 => (orderedInterval (44170811314 / 1000000000000) (44170811315 / 1000000000000), orderedInterval (26601794593 / 1000000000000) (26601794594 / 1000000000000))
    | 21 => (orderedInterval (-34719480890 / 1000000000000) (-34719480889 / 1000000000000), orderedInterval (-61080939307 / 1000000000000) (-61080939306 / 1000000000000))
    | 22 => (orderedInterval (-37478728899 / 1000000000000) (-37478728898 / 1000000000000), orderedInterval (-20426946749 / 1000000000000) (-20426946748 / 1000000000000))
    | 23 => (orderedInterval (-7403997643 / 1000000000000) (-7403997635 / 1000000000000), orderedInterval (35800535555 / 1000000000000) (35800535563 / 1000000000000))
    | 24 => (orderedInterval (52775912283 / 1000000000000) (52775912284 / 1000000000000), orderedInterval (19212041437 / 1000000000000) (19212041438 / 1000000000000))
    | 25 => (orderedInterval (2721628792 / 1000000000000) (2721628793 / 1000000000000), orderedInterval (-27747606045 / 1000000000000) (-27747606044 / 1000000000000))
    | _ => (orderedInterval (32378359527 / 1000000000000) (32378359535 / 1000000000000), orderedInterval (10706420687 / 1000000000000) (10706420694 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13139365213 / 1000000000000) (13139365283 / 1000000000000)
      | 1 => orderedInterval (-2289865318 / 1000000000000) (-2289865265 / 1000000000000)
      | 2 => orderedInterval (1424457783 / 1000000000000) (1424459147 / 1000000000000)
      | 3 => orderedInterval (-2534466115 / 1000000000000) (-2534465422 / 1000000000000)
      | 4 => orderedInterval (2460617637 / 1000000000000) (2460617701 / 1000000000000)
      | 5 => orderedInterval (383421464 / 1000000000000) (383421744 / 1000000000000)
      | 6 => orderedInterval (7830174352 / 1000000000000) (7830188652 / 1000000000000)
      | 7 => orderedInterval (2058808013 / 1000000000000) (2058808067 / 1000000000000)
      | _ => orderedInterval (-5978434121 / 1000000000000) (-5978433997 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-90851870 / 1000000000000) (-90851798 / 1000000000000)
      | 1 => orderedInterval (-4245157509 / 1000000000000) (-4245157448 / 1000000000000)
      | 2 => orderedInterval (-1241728265 / 1000000000000) (-1241726022 / 1000000000000)
      | 3 => orderedInterval (-10749838316 / 1000000000000) (-10749836770 / 1000000000000)
      | 4 => orderedInterval (781280628 / 1000000000000) (781280730 / 1000000000000)
      | 5 => orderedInterval (1869676434 / 1000000000000) (1869676868 / 1000000000000)
      | 6 => orderedInterval (-4341934612 / 1000000000000) (-4341920012 / 1000000000000)
      | 7 => orderedInterval (-2271875765 / 1000000000000) (-2271875717 / 1000000000000)
      | _ => orderedInterval (1757900844 / 1000000000000) (1757901018 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12728853151 / 1000000000000) (-12728853075 / 1000000000000)
      | 1 => orderedInterval (1312197211 / 1000000000000) (1312197295 / 1000000000000)
      | 2 => orderedInterval (-4282711696 / 1000000000000) (-4282707917 / 1000000000000)
      | 3 => orderedInterval (7425568064 / 1000000000000) (7425571553 / 1000000000000)
      | 4 => orderedInterval (-4803167086 / 1000000000000) (-4803166918 / 1000000000000)
      | 5 => orderedInterval (525237601 / 1000000000000) (525238288 / 1000000000000)
      | 6 => orderedInterval (-6748676684 / 1000000000000) (-6748661737 / 1000000000000)
      | 7 => orderedInterval (-1247226014 / 1000000000000) (-1247225966 / 1000000000000)
      | _ => orderedInterval (10066607356 / 1000000000000) (10066607612 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (861566080 / 1000000000000) (861566162 / 1000000000000)
      | 1 => orderedInterval (8475238801 / 1000000000000) (8475238926 / 1000000000000)
      | 2 => orderedInterval (4233035034 / 1000000000000) (4233041543 / 1000000000000)
      | 3 => orderedInterval (46817597488 / 1000000000000) (46817605389 / 1000000000000)
      | 4 => orderedInterval (-1101894867 / 1000000000000) (-1101894584 / 1000000000000)
      | 5 => orderedInterval (-2862868145 / 1000000000000) (-2862867040 / 1000000000000)
      | 6 => orderedInterval (4406098288 / 1000000000000) (4406113560 / 1000000000000)
      | 7 => orderedInterval (3217920964 / 1000000000000) (3217921013 / 1000000000000)
      | _ => orderedInterval (-10706037490 / 1000000000000) (-10706037097 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (11978535484 / 1000000000000) (11978535573 / 1000000000000)
      | 1 => orderedInterval (-2375438610 / 1000000000000) (-2375438417 / 1000000000000)
      | 2 => orderedInterval (14015728708 / 1000000000000) (14015740189 / 1000000000000)
      | 3 => orderedInterval (-31591429782 / 1000000000000) (-31591411806 / 1000000000000)
      | 4 => orderedInterval (6849024019 / 1000000000000) (6849024506 / 1000000000000)
      | 5 => orderedInterval (-4963316783 / 1000000000000) (-4963314972 / 1000000000000)
      | 6 => orderedInterval (6467589884 / 1000000000000) (6467605526 / 1000000000000)
      | 7 => orderedInterval (1102213105 / 1000000000000) (1102213157 / 1000000000000)
      | _ => orderedInterval (-17041465768 / 1000000000000) (-17041465137 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (16494078908 / 1000000000000) (16494095910 / 1000000000000)
    | 1 => orderedInterval (-18532528431 / 1000000000000) (-18532509151 / 1000000000000)
    | 2 => orderedInterval (-10481024399 / 1000000000000) (-10481000865 / 1000000000000)
    | 3 => orderedInterval (53340656153 / 1000000000000) (53340687872 / 1000000000000)
    | _ => orderedInterval (-15558559743 / 1000000000000) (-15558511381 / 1000000000000)

theorem compactCertificate569_stateChecks0 :
    compactCertificate569.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (881 / 2)) (orderedInterval (37791867921 / 1000000000000) (37791868004 / 1000000000000), orderedInterval (4079557741 / 1000000000000) (4079557824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1297881225100781 / 4000000000000)) (orderedInterval (-44071342404 / 1000000000000) (-44071341795 / 1000000000000), orderedInterval (4511149443 / 1000000000000) (4511150052 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (419708121544973 / 800000000000)) (orderedInterval (-24357891183 / 1000000000000) (-24357891182 / 1000000000000), orderedInterval (-24879507169 / 1000000000000) (-24879507168 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_stateChecks1 :
    compactCertificate569.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (378718504522567 / 4000000000000)) (orderedInterval (76889764936 / 1000000000000) (76889764937 / 1000000000000), orderedInterval (28086575818 / 1000000000000) (28086575819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1017291174311899 / 4000000000000)) (orderedInterval (-29826439441 / 1000000000000) (-29826439440 / 1000000000000), orderedInterval (-40110762603 / 1000000000000) (-40110762602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2762143429572783 / 4000000000000)) (orderedInterval (5157579506 / 1000000000000) (5157579507 / 1000000000000), orderedInterval (29918180302 / 1000000000000) (29918180303 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_stateChecks2 :
    compactCertificate569.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2034582348624679 / 4000000000000)) (orderedInterval (16734911158 / 1000000000000) (16734911159 / 1000000000000), orderedInterval (31153102470 / 1000000000000) (31153102471 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (3486291532713667 / 4000000000000)) (orderedInterval (-22809154410 / 1000000000000) (-22809138956 / 1000000000000), orderedInterval (14510286855 / 1000000000000) (14510302310 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2567986563866953 / 4000000000000)) (orderedInterval (29830018418 / 1000000000000) (29830054087 / 1000000000000), orderedInterval (-10112523344 / 1000000000000) (-10112487676 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_stateChecks3 :
    compactCertificate569.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 314 12 (3939951776354119 / 4000000000000)) (orderedInterval (-16121307050 / 1000000000000) (-16121306826 / 1000000000000), orderedInterval (19665901447 / 1000000000000) (19665901670 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2274732218671951 / 4000000000000)) (orderedInterval (-24913715709 / 1000000000000) (-24913715708 / 1000000000000), orderedInterval (-22311253534 / 1000000000000) (-22311253533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 321 12 (4036552239770459 / 4000000000000)) (orderedInterval (-24994576259 / 1000000000000) (-24994572893 / 1000000000000), orderedInterval (-2462722750 / 1000000000000) (-2462719384 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_stateChecks4 :
    compactCertificate569.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 300 12 (3771470710178471 / 4000000000000)) (orderedInterval (23977123215 / 1000000000000) (23977123267 / 1000000000000), orderedInterval (10001911239 / 1000000000000) (10001911291 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2691499458169943 / 4000000000000)) (orderedInterval (30073339888 / 1000000000000) (30073339990 / 1000000000000), orderedInterval (6436221259 / 1000000000000) (6436221361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3051873522935697 / 4000000000000)) (orderedInterval (-9812622543 / 1000000000000) (-9812622542 / 1000000000000), orderedInterval (-27161771589 / 1000000000000) (-27161771588 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_stateChecks5 :
    compactCertificate569.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2544333969614593 / 4000000000000)) (orderedInterval (24274258729 / 1000000000000) (24274272674 / 1000000000000), orderedInterval (-20307090694 / 1000000000000) (-20307076749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2247996224062453 / 4000000000000)) (orderedInterval (-14309751249 / 1000000000000) (-14309751248 / 1000000000000), orderedInterval (-30450502534 / 1000000000000) (-30450502533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (651556925594847 / 800000000000)) (orderedInterval (-27956200369 / 1000000000000) (-27956197413 / 1000000000000), orderedInterval (-315307638 / 1000000000000) (-315304682 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_stateChecks6 :
    compactCertificate569.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1802240745757709 / 4000000000000)) (orderedInterval (-32493675105 / 1000000000000) (-32493586958 / 1000000000000), orderedInterval (18933503474 / 1000000000000) (18933591621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1527779439448549 / 4000000000000)) (orderedInterval (-21143175473 / 1000000000000) (-21143173803 / 1000000000000), orderedInterval (34952615881 / 1000000000000) (34952617551 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (956013436133047 / 4000000000000)) (orderedInterval (44170811314 / 1000000000000) (44170811315 / 1000000000000), orderedInterval (26601794593 / 1000000000000) (26601794594 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_stateChecks7 :
    compactCertificate569.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (514147205509449 / 4000000000000)) (orderedInterval (-34719480890 / 1000000000000) (-34719480889 / 1000000000000), orderedInterval (-61080939307 / 1000000000000) (-61080939306 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1396009678835347 / 4000000000000)) (orderedInterval (-37478728899 / 1000000000000) (-37478728898 / 1000000000000), orderedInterval (-20426946749 / 1000000000000) (-20426946748 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1906131867911219 / 4000000000000)) (orderedInterval (-7403997643 / 1000000000000) (-7403997635 / 1000000000000), orderedInterval (35800535555 / 1000000000000) (35800535563 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_stateChecks8 :
    compactCertificate569.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (805986563866953 / 4000000000000)) (orderedInterval (52775912283 / 1000000000000) (52775912284 / 1000000000000), orderedInterval (19212041437 / 1000000000000) (19212041438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (3276290635083113 / 4000000000000)) (orderedInterval (2721628792 / 1000000000000) (2721628793 / 1000000000000), orderedInterval (-27747606045 / 1000000000000) (-27747606044 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2188410307613767 / 4000000000000)) (orderedInterval (32378359527 / 1000000000000) (32378359535 / 1000000000000), orderedInterval (10706420687 / 1000000000000) (10706420694 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_states : ∀ j,
    BesselStateValid (compactCertificate569.point j) (compactCertificate569.state j) :=
  compactCertificate569.statesValid_of_checks3 compactCertificate569_stateChecks0
    compactCertificate569_stateChecks1 compactCertificate569_stateChecks2
    compactCertificate569_stateChecks3 compactCertificate569_stateChecks4
    compactCertificate569_stateChecks5 compactCertificate569_stateChecks6
    compactCertificate569_stateChecks7 compactCertificate569_stateChecks8

theorem compactCertificate569_chunkChecks0_0 :
    compactCertificate569.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (881 / 2) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791867921 / 1000000000000) (37791868004 / 1000000000000), orderedInterval (4079557741 / 1000000000000) (4079557824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1297881225100781 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44071342404 / 1000000000000) (-44071341795 / 1000000000000), orderedInterval (4511149443 / 1000000000000) (4511150052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (419708121544973 / 800000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24357891183 / 1000000000000) (-24357891182 / 1000000000000), orderedInterval (-24879507169 / 1000000000000) (-24879507168 / 1000000000000)))) (orderedInterval (13139365213 / 1000000000000) (13139365283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (378718504522567 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76889764936 / 1000000000000) (76889764937 / 1000000000000), orderedInterval (28086575818 / 1000000000000) (28086575819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1017291174311899 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29826439441 / 1000000000000) (-29826439440 / 1000000000000), orderedInterval (-40110762603 / 1000000000000) (-40110762602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2762143429572783 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5157579506 / 1000000000000) (5157579507 / 1000000000000), orderedInterval (29918180302 / 1000000000000) (29918180303 / 1000000000000)))) (orderedInterval (-2289865318 / 1000000000000) (-2289865265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2034582348624679 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16734911158 / 1000000000000) (16734911159 / 1000000000000), orderedInterval (31153102470 / 1000000000000) (31153102471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3486291532713667 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22809154410 / 1000000000000) (-22809138956 / 1000000000000), orderedInterval (14510286855 / 1000000000000) (14510302310 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2567986563866953 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29830018418 / 1000000000000) (29830054087 / 1000000000000), orderedInterval (-10112523344 / 1000000000000) (-10112487676 / 1000000000000)))) (orderedInterval (1424457783 / 1000000000000) (1424459147 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks0_1 :
    compactCertificate569.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3939951776354119 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16121307050 / 1000000000000) (-16121306826 / 1000000000000), orderedInterval (19665901447 / 1000000000000) (19665901670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2274732218671951 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24913715709 / 1000000000000) (-24913715708 / 1000000000000), orderedInterval (-22311253534 / 1000000000000) (-22311253533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4036552239770459 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24994576259 / 1000000000000) (-24994572893 / 1000000000000), orderedInterval (-2462722750 / 1000000000000) (-2462719384 / 1000000000000)))) (orderedInterval (-2534466115 / 1000000000000) (-2534465422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3771470710178471 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23977123215 / 1000000000000) (23977123267 / 1000000000000), orderedInterval (10001911239 / 1000000000000) (10001911291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2691499458169943 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30073339888 / 1000000000000) (30073339990 / 1000000000000), orderedInterval (6436221259 / 1000000000000) (6436221361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3051873522935697 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9812622543 / 1000000000000) (-9812622542 / 1000000000000), orderedInterval (-27161771589 / 1000000000000) (-27161771588 / 1000000000000)))) (orderedInterval (2460617637 / 1000000000000) (2460617701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2544333969614593 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24274258729 / 1000000000000) (24274272674 / 1000000000000), orderedInterval (-20307090694 / 1000000000000) (-20307076749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2247996224062453 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14309751249 / 1000000000000) (-14309751248 / 1000000000000), orderedInterval (-30450502534 / 1000000000000) (-30450502533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (651556925594847 / 800000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27956200369 / 1000000000000) (-27956197413 / 1000000000000), orderedInterval (-315307638 / 1000000000000) (-315304682 / 1000000000000)))) (orderedInterval (383421464 / 1000000000000) (383421744 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks0_2 :
    compactCertificate569.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1802240745757709 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32493675105 / 1000000000000) (-32493586958 / 1000000000000), orderedInterval (18933503474 / 1000000000000) (18933591621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1527779439448549 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21143175473 / 1000000000000) (-21143173803 / 1000000000000), orderedInterval (34952615881 / 1000000000000) (34952617551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (956013436133047 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44170811314 / 1000000000000) (44170811315 / 1000000000000), orderedInterval (26601794593 / 1000000000000) (26601794594 / 1000000000000)))) (orderedInterval (7830174352 / 1000000000000) (7830188652 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (514147205509449 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-34719480890 / 1000000000000) (-34719480889 / 1000000000000), orderedInterval (-61080939307 / 1000000000000) (-61080939306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1396009678835347 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37478728899 / 1000000000000) (-37478728898 / 1000000000000), orderedInterval (-20426946749 / 1000000000000) (-20426946748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1906131867911219 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7403997643 / 1000000000000) (-7403997635 / 1000000000000), orderedInterval (35800535555 / 1000000000000) (35800535563 / 1000000000000)))) (orderedInterval (2058808013 / 1000000000000) (2058808067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (805986563866953 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52775912283 / 1000000000000) (52775912284 / 1000000000000), orderedInterval (19212041437 / 1000000000000) (19212041438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3276290635083113 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2721628792 / 1000000000000) (2721628793 / 1000000000000), orderedInterval (-27747606045 / 1000000000000) (-27747606044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2188410307613767 / 4000000000000) 0 (IntervalRat.scale (881 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32378359527 / 1000000000000) (32378359535 / 1000000000000), orderedInterval (10706420687 / 1000000000000) (10706420694 / 1000000000000)))) (orderedInterval (-5978434121 / 1000000000000) (-5978433997 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks0 :
    compactCertificate569.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate569.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate569_chunkChecks0_0
    compactCertificate569_chunkChecks0_1 compactCertificate569_chunkChecks0_2

theorem compactCertificate569_chunkChecks1_0 :
    compactCertificate569.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (881 / 2) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791867921 / 1000000000000) (37791868004 / 1000000000000), orderedInterval (4079557741 / 1000000000000) (4079557824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1297881225100781 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44071342404 / 1000000000000) (-44071341795 / 1000000000000), orderedInterval (4511149443 / 1000000000000) (4511150052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (419708121544973 / 800000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24357891183 / 1000000000000) (-24357891182 / 1000000000000), orderedInterval (-24879507169 / 1000000000000) (-24879507168 / 1000000000000)))) (orderedInterval (-90851870 / 1000000000000) (-90851798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (378718504522567 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76889764936 / 1000000000000) (76889764937 / 1000000000000), orderedInterval (28086575818 / 1000000000000) (28086575819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1017291174311899 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29826439441 / 1000000000000) (-29826439440 / 1000000000000), orderedInterval (-40110762603 / 1000000000000) (-40110762602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2762143429572783 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5157579506 / 1000000000000) (5157579507 / 1000000000000), orderedInterval (29918180302 / 1000000000000) (29918180303 / 1000000000000)))) (orderedInterval (-4245157509 / 1000000000000) (-4245157448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2034582348624679 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16734911158 / 1000000000000) (16734911159 / 1000000000000), orderedInterval (31153102470 / 1000000000000) (31153102471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3486291532713667 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22809154410 / 1000000000000) (-22809138956 / 1000000000000), orderedInterval (14510286855 / 1000000000000) (14510302310 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2567986563866953 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29830018418 / 1000000000000) (29830054087 / 1000000000000), orderedInterval (-10112523344 / 1000000000000) (-10112487676 / 1000000000000)))) (orderedInterval (-1241728265 / 1000000000000) (-1241726022 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks1_1 :
    compactCertificate569.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3939951776354119 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16121307050 / 1000000000000) (-16121306826 / 1000000000000), orderedInterval (19665901447 / 1000000000000) (19665901670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2274732218671951 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24913715709 / 1000000000000) (-24913715708 / 1000000000000), orderedInterval (-22311253534 / 1000000000000) (-22311253533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4036552239770459 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24994576259 / 1000000000000) (-24994572893 / 1000000000000), orderedInterval (-2462722750 / 1000000000000) (-2462719384 / 1000000000000)))) (orderedInterval (-10749838316 / 1000000000000) (-10749836770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3771470710178471 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23977123215 / 1000000000000) (23977123267 / 1000000000000), orderedInterval (10001911239 / 1000000000000) (10001911291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2691499458169943 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30073339888 / 1000000000000) (30073339990 / 1000000000000), orderedInterval (6436221259 / 1000000000000) (6436221361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3051873522935697 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9812622543 / 1000000000000) (-9812622542 / 1000000000000), orderedInterval (-27161771589 / 1000000000000) (-27161771588 / 1000000000000)))) (orderedInterval (781280628 / 1000000000000) (781280730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2544333969614593 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24274258729 / 1000000000000) (24274272674 / 1000000000000), orderedInterval (-20307090694 / 1000000000000) (-20307076749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2247996224062453 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14309751249 / 1000000000000) (-14309751248 / 1000000000000), orderedInterval (-30450502534 / 1000000000000) (-30450502533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (651556925594847 / 800000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27956200369 / 1000000000000) (-27956197413 / 1000000000000), orderedInterval (-315307638 / 1000000000000) (-315304682 / 1000000000000)))) (orderedInterval (1869676434 / 1000000000000) (1869676868 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks1_2 :
    compactCertificate569.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1802240745757709 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32493675105 / 1000000000000) (-32493586958 / 1000000000000), orderedInterval (18933503474 / 1000000000000) (18933591621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1527779439448549 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21143175473 / 1000000000000) (-21143173803 / 1000000000000), orderedInterval (34952615881 / 1000000000000) (34952617551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (956013436133047 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44170811314 / 1000000000000) (44170811315 / 1000000000000), orderedInterval (26601794593 / 1000000000000) (26601794594 / 1000000000000)))) (orderedInterval (-4341934612 / 1000000000000) (-4341920012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (514147205509449 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-34719480890 / 1000000000000) (-34719480889 / 1000000000000), orderedInterval (-61080939307 / 1000000000000) (-61080939306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1396009678835347 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37478728899 / 1000000000000) (-37478728898 / 1000000000000), orderedInterval (-20426946749 / 1000000000000) (-20426946748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1906131867911219 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7403997643 / 1000000000000) (-7403997635 / 1000000000000), orderedInterval (35800535555 / 1000000000000) (35800535563 / 1000000000000)))) (orderedInterval (-2271875765 / 1000000000000) (-2271875717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (805986563866953 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52775912283 / 1000000000000) (52775912284 / 1000000000000), orderedInterval (19212041437 / 1000000000000) (19212041438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3276290635083113 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2721628792 / 1000000000000) (2721628793 / 1000000000000), orderedInterval (-27747606045 / 1000000000000) (-27747606044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2188410307613767 / 4000000000000) 1 (IntervalRat.scale (881 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32378359527 / 1000000000000) (32378359535 / 1000000000000), orderedInterval (10706420687 / 1000000000000) (10706420694 / 1000000000000)))) (orderedInterval (1757900844 / 1000000000000) (1757901018 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks1 :
    compactCertificate569.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate569.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate569_chunkChecks1_0
    compactCertificate569_chunkChecks1_1 compactCertificate569_chunkChecks1_2

theorem compactCertificate569_chunkChecks2_0 :
    compactCertificate569.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (881 / 2) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791867921 / 1000000000000) (37791868004 / 1000000000000), orderedInterval (4079557741 / 1000000000000) (4079557824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1297881225100781 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44071342404 / 1000000000000) (-44071341795 / 1000000000000), orderedInterval (4511149443 / 1000000000000) (4511150052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (419708121544973 / 800000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24357891183 / 1000000000000) (-24357891182 / 1000000000000), orderedInterval (-24879507169 / 1000000000000) (-24879507168 / 1000000000000)))) (orderedInterval (-12728853151 / 1000000000000) (-12728853075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (378718504522567 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76889764936 / 1000000000000) (76889764937 / 1000000000000), orderedInterval (28086575818 / 1000000000000) (28086575819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1017291174311899 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29826439441 / 1000000000000) (-29826439440 / 1000000000000), orderedInterval (-40110762603 / 1000000000000) (-40110762602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2762143429572783 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5157579506 / 1000000000000) (5157579507 / 1000000000000), orderedInterval (29918180302 / 1000000000000) (29918180303 / 1000000000000)))) (orderedInterval (1312197211 / 1000000000000) (1312197295 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2034582348624679 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16734911158 / 1000000000000) (16734911159 / 1000000000000), orderedInterval (31153102470 / 1000000000000) (31153102471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3486291532713667 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22809154410 / 1000000000000) (-22809138956 / 1000000000000), orderedInterval (14510286855 / 1000000000000) (14510302310 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2567986563866953 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29830018418 / 1000000000000) (29830054087 / 1000000000000), orderedInterval (-10112523344 / 1000000000000) (-10112487676 / 1000000000000)))) (orderedInterval (-4282711696 / 1000000000000) (-4282707917 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks2_1 :
    compactCertificate569.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3939951776354119 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16121307050 / 1000000000000) (-16121306826 / 1000000000000), orderedInterval (19665901447 / 1000000000000) (19665901670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2274732218671951 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24913715709 / 1000000000000) (-24913715708 / 1000000000000), orderedInterval (-22311253534 / 1000000000000) (-22311253533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4036552239770459 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24994576259 / 1000000000000) (-24994572893 / 1000000000000), orderedInterval (-2462722750 / 1000000000000) (-2462719384 / 1000000000000)))) (orderedInterval (7425568064 / 1000000000000) (7425571553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3771470710178471 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23977123215 / 1000000000000) (23977123267 / 1000000000000), orderedInterval (10001911239 / 1000000000000) (10001911291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2691499458169943 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30073339888 / 1000000000000) (30073339990 / 1000000000000), orderedInterval (6436221259 / 1000000000000) (6436221361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3051873522935697 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9812622543 / 1000000000000) (-9812622542 / 1000000000000), orderedInterval (-27161771589 / 1000000000000) (-27161771588 / 1000000000000)))) (orderedInterval (-4803167086 / 1000000000000) (-4803166918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2544333969614593 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24274258729 / 1000000000000) (24274272674 / 1000000000000), orderedInterval (-20307090694 / 1000000000000) (-20307076749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2247996224062453 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14309751249 / 1000000000000) (-14309751248 / 1000000000000), orderedInterval (-30450502534 / 1000000000000) (-30450502533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (651556925594847 / 800000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27956200369 / 1000000000000) (-27956197413 / 1000000000000), orderedInterval (-315307638 / 1000000000000) (-315304682 / 1000000000000)))) (orderedInterval (525237601 / 1000000000000) (525238288 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks2_2 :
    compactCertificate569.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1802240745757709 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32493675105 / 1000000000000) (-32493586958 / 1000000000000), orderedInterval (18933503474 / 1000000000000) (18933591621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1527779439448549 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21143175473 / 1000000000000) (-21143173803 / 1000000000000), orderedInterval (34952615881 / 1000000000000) (34952617551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (956013436133047 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44170811314 / 1000000000000) (44170811315 / 1000000000000), orderedInterval (26601794593 / 1000000000000) (26601794594 / 1000000000000)))) (orderedInterval (-6748676684 / 1000000000000) (-6748661737 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (514147205509449 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-34719480890 / 1000000000000) (-34719480889 / 1000000000000), orderedInterval (-61080939307 / 1000000000000) (-61080939306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1396009678835347 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37478728899 / 1000000000000) (-37478728898 / 1000000000000), orderedInterval (-20426946749 / 1000000000000) (-20426946748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1906131867911219 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7403997643 / 1000000000000) (-7403997635 / 1000000000000), orderedInterval (35800535555 / 1000000000000) (35800535563 / 1000000000000)))) (orderedInterval (-1247226014 / 1000000000000) (-1247225966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (805986563866953 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52775912283 / 1000000000000) (52775912284 / 1000000000000), orderedInterval (19212041437 / 1000000000000) (19212041438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3276290635083113 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2721628792 / 1000000000000) (2721628793 / 1000000000000), orderedInterval (-27747606045 / 1000000000000) (-27747606044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2188410307613767 / 4000000000000) 2 (IntervalRat.scale (881 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32378359527 / 1000000000000) (32378359535 / 1000000000000), orderedInterval (10706420687 / 1000000000000) (10706420694 / 1000000000000)))) (orderedInterval (10066607356 / 1000000000000) (10066607612 / 1000000000000))) = true
  rfl'

theorem compactCertificate569_chunkChecks2 :
    compactCertificate569.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate569.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate569_chunkChecks2_0
    compactCertificate569_chunkChecks2_1 compactCertificate569_chunkChecks2_2

theorem compactCertificate569_chunkChecks3_0 :
    compactCertificate569.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (881 / 2) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791867921 / 1000000000000) (37791868004 / 1000000000000), orderedInterval (4079557741 / 1000000000000) (4079557824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1297881225100781 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44071342404 / 1000000000000) (-44071341795 / 1000000000000), orderedInterval (4511149443 / 1000000000000) (4511150052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (419708121544973 / 800000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24357891183 / 1000000000000) (-24357891182 / 1000000000000), orderedInterval (-24879507169 / 1000000000000) (-24879507168 / 1000000000000)))) (orderedInterval (861566080 / 1000000000000) (861566162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (378718504522567 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76889764936 / 1000000000000) (76889764937 / 1000000000000), orderedInterval (28086575818 / 1000000000000) (28086575819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1017291174311899 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29826439441 / 1000000000000) (-29826439440 / 1000000000000), orderedInterval (-40110762603 / 1000000000000) (-40110762602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2762143429572783 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5157579506 / 1000000000000) (5157579507 / 1000000000000), orderedInterval (29918180302 / 1000000000000) (29918180303 / 1000000000000)))) (orderedInterval (8475238801 / 1000000000000) (8475238926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2034582348624679 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16734911158 / 1000000000000) (16734911159 / 1000000000000), orderedInterval (31153102470 / 1000000000000) (31153102471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3486291532713667 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22809154410 / 1000000000000) (-22809138956 / 1000000000000), orderedInterval (14510286855 / 1000000000000) (14510302310 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2567986563866953 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29830018418 / 1000000000000) (29830054087 / 1000000000000), orderedInterval (-10112523344 / 1000000000000) (-10112487676 / 1000000000000)))) (orderedInterval (4233035034 / 1000000000000) (4233041543 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate569_chunkChecks3_1 :
    compactCertificate569.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3939951776354119 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16121307050 / 1000000000000) (-16121306826 / 1000000000000), orderedInterval (19665901447 / 1000000000000) (19665901670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2274732218671951 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24913715709 / 1000000000000) (-24913715708 / 1000000000000), orderedInterval (-22311253534 / 1000000000000) (-22311253533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4036552239770459 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24994576259 / 1000000000000) (-24994572893 / 1000000000000), orderedInterval (-2462722750 / 1000000000000) (-2462719384 / 1000000000000)))) (orderedInterval (46817597488 / 1000000000000) (46817605389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3771470710178471 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23977123215 / 1000000000000) (23977123267 / 1000000000000), orderedInterval (10001911239 / 1000000000000) (10001911291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2691499458169943 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30073339888 / 1000000000000) (30073339990 / 1000000000000), orderedInterval (6436221259 / 1000000000000) (6436221361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3051873522935697 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9812622543 / 1000000000000) (-9812622542 / 1000000000000), orderedInterval (-27161771589 / 1000000000000) (-27161771588 / 1000000000000)))) (orderedInterval (-1101894867 / 1000000000000) (-1101894584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2544333969614593 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24274258729 / 1000000000000) (24274272674 / 1000000000000), orderedInterval (-20307090694 / 1000000000000) (-20307076749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2247996224062453 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14309751249 / 1000000000000) (-14309751248 / 1000000000000), orderedInterval (-30450502534 / 1000000000000) (-30450502533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (651556925594847 / 800000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27956200369 / 1000000000000) (-27956197413 / 1000000000000), orderedInterval (-315307638 / 1000000000000) (-315304682 / 1000000000000)))) (orderedInterval (-2862868145 / 1000000000000) (-2862867040 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate569_chunkChecks3_2 :
    compactCertificate569.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1802240745757709 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32493675105 / 1000000000000) (-32493586958 / 1000000000000), orderedInterval (18933503474 / 1000000000000) (18933591621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1527779439448549 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21143175473 / 1000000000000) (-21143173803 / 1000000000000), orderedInterval (34952615881 / 1000000000000) (34952617551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (956013436133047 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44170811314 / 1000000000000) (44170811315 / 1000000000000), orderedInterval (26601794593 / 1000000000000) (26601794594 / 1000000000000)))) (orderedInterval (4406098288 / 1000000000000) (4406113560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (514147205509449 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-34719480890 / 1000000000000) (-34719480889 / 1000000000000), orderedInterval (-61080939307 / 1000000000000) (-61080939306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1396009678835347 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37478728899 / 1000000000000) (-37478728898 / 1000000000000), orderedInterval (-20426946749 / 1000000000000) (-20426946748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1906131867911219 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7403997643 / 1000000000000) (-7403997635 / 1000000000000), orderedInterval (35800535555 / 1000000000000) (35800535563 / 1000000000000)))) (orderedInterval (3217920964 / 1000000000000) (3217921013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (805986563866953 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52775912283 / 1000000000000) (52775912284 / 1000000000000), orderedInterval (19212041437 / 1000000000000) (19212041438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3276290635083113 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2721628792 / 1000000000000) (2721628793 / 1000000000000), orderedInterval (-27747606045 / 1000000000000) (-27747606044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2188410307613767 / 4000000000000) 3 (IntervalRat.scale (881 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32378359527 / 1000000000000) (32378359535 / 1000000000000), orderedInterval (10706420687 / 1000000000000) (10706420694 / 1000000000000)))) (orderedInterval (-10706037490 / 1000000000000) (-10706037097 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate569_chunkChecks3 :
    compactCertificate569.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate569.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate569_chunkChecks3_0
    compactCertificate569_chunkChecks3_1 compactCertificate569_chunkChecks3_2

theorem compactCertificate569_chunkChecks4_0 :
    compactCertificate569.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (881 / 2) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791867921 / 1000000000000) (37791868004 / 1000000000000), orderedInterval (4079557741 / 1000000000000) (4079557824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1297881225100781 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44071342404 / 1000000000000) (-44071341795 / 1000000000000), orderedInterval (4511149443 / 1000000000000) (4511150052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (419708121544973 / 800000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24357891183 / 1000000000000) (-24357891182 / 1000000000000), orderedInterval (-24879507169 / 1000000000000) (-24879507168 / 1000000000000)))) (orderedInterval (11978535484 / 1000000000000) (11978535573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (378718504522567 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76889764936 / 1000000000000) (76889764937 / 1000000000000), orderedInterval (28086575818 / 1000000000000) (28086575819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1017291174311899 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29826439441 / 1000000000000) (-29826439440 / 1000000000000), orderedInterval (-40110762603 / 1000000000000) (-40110762602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2762143429572783 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5157579506 / 1000000000000) (5157579507 / 1000000000000), orderedInterval (29918180302 / 1000000000000) (29918180303 / 1000000000000)))) (orderedInterval (-2375438610 / 1000000000000) (-2375438417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2034582348624679 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16734911158 / 1000000000000) (16734911159 / 1000000000000), orderedInterval (31153102470 / 1000000000000) (31153102471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3486291532713667 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22809154410 / 1000000000000) (-22809138956 / 1000000000000), orderedInterval (14510286855 / 1000000000000) (14510302310 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2567986563866953 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29830018418 / 1000000000000) (29830054087 / 1000000000000), orderedInterval (-10112523344 / 1000000000000) (-10112487676 / 1000000000000)))) (orderedInterval (14015728708 / 1000000000000) (14015740189 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate569_chunkChecks4_1 :
    compactCertificate569.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3939951776354119 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16121307050 / 1000000000000) (-16121306826 / 1000000000000), orderedInterval (19665901447 / 1000000000000) (19665901670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2274732218671951 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24913715709 / 1000000000000) (-24913715708 / 1000000000000), orderedInterval (-22311253534 / 1000000000000) (-22311253533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4036552239770459 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24994576259 / 1000000000000) (-24994572893 / 1000000000000), orderedInterval (-2462722750 / 1000000000000) (-2462719384 / 1000000000000)))) (orderedInterval (-31591429782 / 1000000000000) (-31591411806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3771470710178471 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23977123215 / 1000000000000) (23977123267 / 1000000000000), orderedInterval (10001911239 / 1000000000000) (10001911291 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2691499458169943 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30073339888 / 1000000000000) (30073339990 / 1000000000000), orderedInterval (6436221259 / 1000000000000) (6436221361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3051873522935697 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9812622543 / 1000000000000) (-9812622542 / 1000000000000), orderedInterval (-27161771589 / 1000000000000) (-27161771588 / 1000000000000)))) (orderedInterval (6849024019 / 1000000000000) (6849024506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2544333969614593 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24274258729 / 1000000000000) (24274272674 / 1000000000000), orderedInterval (-20307090694 / 1000000000000) (-20307076749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2247996224062453 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14309751249 / 1000000000000) (-14309751248 / 1000000000000), orderedInterval (-30450502534 / 1000000000000) (-30450502533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (651556925594847 / 800000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27956200369 / 1000000000000) (-27956197413 / 1000000000000), orderedInterval (-315307638 / 1000000000000) (-315304682 / 1000000000000)))) (orderedInterval (-4963316783 / 1000000000000) (-4963314972 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate569_chunkChecks4_2 :
    compactCertificate569.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1802240745757709 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-32493675105 / 1000000000000) (-32493586958 / 1000000000000), orderedInterval (18933503474 / 1000000000000) (18933591621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1527779439448549 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-21143175473 / 1000000000000) (-21143173803 / 1000000000000), orderedInterval (34952615881 / 1000000000000) (34952617551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (956013436133047 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44170811314 / 1000000000000) (44170811315 / 1000000000000), orderedInterval (26601794593 / 1000000000000) (26601794594 / 1000000000000)))) (orderedInterval (6467589884 / 1000000000000) (6467605526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (514147205509449 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-34719480890 / 1000000000000) (-34719480889 / 1000000000000), orderedInterval (-61080939307 / 1000000000000) (-61080939306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1396009678835347 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37478728899 / 1000000000000) (-37478728898 / 1000000000000), orderedInterval (-20426946749 / 1000000000000) (-20426946748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1906131867911219 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7403997643 / 1000000000000) (-7403997635 / 1000000000000), orderedInterval (35800535555 / 1000000000000) (35800535563 / 1000000000000)))) (orderedInterval (1102213105 / 1000000000000) (1102213157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (805986563866953 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52775912283 / 1000000000000) (52775912284 / 1000000000000), orderedInterval (19212041437 / 1000000000000) (19212041438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3276290635083113 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2721628792 / 1000000000000) (2721628793 / 1000000000000), orderedInterval (-27747606045 / 1000000000000) (-27747606044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2188410307613767 / 4000000000000) 4 (IntervalRat.scale (881 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32378359527 / 1000000000000) (32378359535 / 1000000000000), orderedInterval (10706420687 / 1000000000000) (10706420694 / 1000000000000)))) (orderedInterval (-17041465768 / 1000000000000) (-17041465137 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate569_chunkChecks4 :
    compactCertificate569.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate569.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate569_chunkChecks4_0
    compactCertificate569_chunkChecks4_1 compactCertificate569_chunkChecks4_2

theorem compactCertificate569_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate569.chunkCheck r b = true :=
  compactCertificate569.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate569_chunkChecks0
    · exact compactCertificate569_chunkChecks1
    · exact compactCertificate569_chunkChecks2
    · exact compactCertificate569_chunkChecks3
    · exact compactCertificate569_chunkChecks4)

theorem compactCertificate569_coefficient0 :
    compactCertificate569.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate569_coefficient1 :
    compactCertificate569.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate569_coefficient2 :
    compactCertificate569.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate569_coefficient3 :
    compactCertificate569.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate569_coefficient4 :
    compactCertificate569.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate569_coefficients : ∀ r : Fin 5,
    compactCertificate569.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate569_coefficient0
  · exact compactCertificate569_coefficient1
  · exact compactCertificate569_coefficient2
  · exact compactCertificate569_coefficient3
  · exact compactCertificate569_coefficient4

theorem compactCertificate569_lower : (1 : ℚ) ≤ compactCertificate569.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate569, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate569_proves {t : ℝ} (ht : t ∈ compactCertificate569.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate569.proves compactCertificate569_states compactCertificate569_chunks
    compactCertificate569_coefficients compactCertificate569_lower ht

end Erdos232
