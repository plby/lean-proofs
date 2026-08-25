/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate482 : CompactCertificate where
  left := 353
  right := 354
  center := 707 / 2
  grid := fun i =>
    match i.val with
    | 0 => 113
    | 1 => 83
    | 2 => 134
    | 3 => 24
    | 4 => 65
    | 5 => 176
    | 6 => 130
    | 7 => 223
    | 8 => 164
    | 9 => 252
    | 10 => 145
    | 11 => 258
    | 12 => 241
    | 13 => 172
    | 14 => 195
    | 15 => 163
    | 16 => 144
    | 17 => 208
    | 18 => 115
    | 19 => 98
    | 20 => 61
    | 21 => 33
    | 22 => 89
    | 23 => 122
    | 24 => 51
    | 25 => 209
    | _ => 140
  point := fun i =>
    match i.val with
    | 0 => 707 / 2
    | 1 => 1041546000166007 / 4000000000000
    | 2 => 336814576540631 / 800000000000
    | 3 => 303920525195749 / 4000000000000
    | 4 => 816373280633953 / 4000000000000
    | 5 => 2216612264140701 / 4000000000000
    | 6 => 1632746561268613 / 4000000000000
    | 7 => 2797739062007449 / 4000000000000
    | 8 => 2060801930367691 / 4000000000000
    | 9 => 3161800120184293 / 4000000000000
    | 10 => 1825466150511997 / 4000000000000
    | 11 => 3239321717954273 / 4000000000000
    | 12 => 3026594542674437 / 4000000000000
    | 13 => 2159920677555221 / 4000000000000
    | 14 => 2449119841901859 / 4000000000000
    | 15 => 2041820790598771 / 4000000000000
    | 16 => 1804010590706191 / 4000000000000
    | 17 => 522872583876909 / 800000000000
    | 18 => 1446293084280023 / 4000000000000
    | 19 => 1226038664801503 / 4000000000000
    | 20 => 767198069632309 / 4000000000000
    | 21 => 412601673433803 / 4000000000000
    | 22 => 1120293805830409 / 4000000000000
    | 23 => 1529665414997993 / 4000000000000
    | 24 => 646801930367691 / 4000000000000
    | 25 => 2629213937575211 / 4000000000000
    | _ => 1756193061842149 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (27820065828 / 1000000000000) (27820077692 / 1000000000000), orderedInterval (-32085391418 / 1000000000000) (-32085379553 / 1000000000000))
    | 1 => (orderedInterval (-20127224269 / 1000000000000) (-20127224268 / 1000000000000), orderedInterval (-45125507537 / 1000000000000) (-45125507536 / 1000000000000))
    | 2 => (orderedInterval (28692490085 / 1000000000000) (28692490086 / 1000000000000), orderedInterval (26211618952 / 1000000000000) (26211618953 / 1000000000000))
    | 3 => (orderedInterval (89615439608 / 1000000000000) (89615439609 / 1000000000000), orderedInterval (18056289805 / 1000000000000) (18056289807 / 1000000000000))
    | 4 => (orderedInterval (-34882494051 / 1000000000000) (-34882494050 / 1000000000000), orderedInterval (-43531878325 / 1000000000000) (-43531878324 / 1000000000000))
    | 5 => (orderedInterval (30561987046 / 1000000000000) (30562057016 / 1000000000000), orderedInterval (-14682923144 / 1000000000000) (-14682853175 / 1000000000000))
    | 6 => (orderedInterval (21134276844 / 1000000000000) (21134276845 / 1000000000000), orderedInterval (33335346517 / 1000000000000) (33335346518 / 1000000000000))
    | 7 => (orderedInterval (10491587339 / 1000000000000) (10491587354 / 1000000000000), orderedInterval (-28293866884 / 1000000000000) (-28293866869 / 1000000000000))
    | 8 => (orderedInterval (24330031156 / 1000000000000) (24330031157 / 1000000000000), orderedInterval (25348094011 / 1000000000000) (25348094012 / 1000000000000))
    | 9 => (orderedInterval (-12243747725 / 1000000000000) (-12243747695 / 1000000000000), orderedInterval (25610083728 / 1000000000000) (25610083758 / 1000000000000))
    | 10 => (orderedInterval (-37302801348 / 1000000000000) (-37302800605 / 1000000000000), orderedInterval (1904977818 / 1000000000000) (1904978561 / 1000000000000))
    | 11 => (orderedInterval (2373876450 / 1000000000000) (2373876451 / 1000000000000), orderedInterval (27935602272 / 1000000000000) (27935602273 / 1000000000000))
    | 12 => (orderedInterval (-8849714085 / 1000000000000) (-8849714084 / 1000000000000), orderedInterval (-27617520336 / 1000000000000) (-27617520335 / 1000000000000))
    | 13 => (orderedInterval (13730754740 / 1000000000000) (13730754741 / 1000000000000), orderedInterval (31458471403 / 1000000000000) (31458471404 / 1000000000000))
    | 14 => (orderedInterval (-14158584059 / 1000000000000) (-14158584058 / 1000000000000), orderedInterval (-28958896228 / 1000000000000) (-28958896227 / 1000000000000))
    | 15 => (orderedInterval (26279531005 / 1000000000000) (26279549315 / 1000000000000), orderedInterval (-23616990307 / 1000000000000) (-23616971997 / 1000000000000))
    | 16 => (orderedInterval (-21262831180 / 1000000000000) (-21262829032 / 1000000000000), orderedInterval (30998688412 / 1000000000000) (30998690560 / 1000000000000))
    | 17 => (orderedInterval (24918271546 / 1000000000000) (24918271547 / 1000000000000), orderedInterval (18772263587 / 1000000000000) (18772263588 / 1000000000000))
    | 18 => (orderedInterval (-36911491197 / 1000000000000) (-36911491196 / 1000000000000), orderedInterval (-19904772732 / 1000000000000) (-19904772731 / 1000000000000))
    | 19 => (orderedInterval (-25029915664 / 1000000000000) (-25029911821 / 1000000000000), orderedInterval (38126283521 / 1000000000000) (38126287364 / 1000000000000))
    | 20 => (orderedInterval (-46765797734 / 1000000000000) (-46765797733 / 1000000000000), orderedInterval (-33525530227 / 1000000000000) (-33525530226 / 1000000000000))
    | 21 => (orderedInterval (-20351652845 / 1000000000000) (-20351652844 / 1000000000000), orderedInterval (-75780429509 / 1000000000000) (-75780429508 / 1000000000000))
    | 22 => (orderedInterval (-45343276911 / 1000000000000) (-45343276909 / 1000000000000), orderedInterval (-14650991905 / 1000000000000) (-14650991903 / 1000000000000))
    | 23 => (orderedInterval (-2970897777 / 1000000000000) (-2970897775 / 1000000000000), orderedInterval (40696692581 / 1000000000000) (40696692583 / 1000000000000))
    | 24 => (orderedInterval (-48268866077 / 1000000000000) (-48268761576 / 1000000000000), orderedInterval (40238456791 / 1000000000000) (40238561292 / 1000000000000))
    | 25 => (orderedInterval (-31033836058 / 1000000000000) (-31033835499 / 1000000000000), orderedInterval (-2307323882 / 1000000000000) (-2307323323 / 1000000000000))
    | _ => (orderedInterval (396295222 / 1000000000000) (396295223 / 1000000000000), orderedInterval (38076357983 / 1000000000000) (38076357984 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (12523061529 / 1000000000000) (12523066256 / 1000000000000)
      | 1 => orderedInterval (-4418530428 / 1000000000000) (-4418525411 / 1000000000000)
      | 2 => orderedInterval (264406309 / 1000000000000) (264406330 / 1000000000000)
      | 3 => orderedInterval (-250804027 / 1000000000000) (-250803826 / 1000000000000)
      | 4 => orderedInterval (1529834739 / 1000000000000) (1529834782 / 1000000000000)
      | 5 => orderedInterval (2158274562 / 1000000000000) (2158274931 / 1000000000000)
      | 6 => orderedInterval (5796087110 / 1000000000000) (5796087416 / 1000000000000)
      | 7 => orderedInterval (1632178544 / 1000000000000) (1632178587 / 1000000000000)
      | _ => orderedInterval (2160873254 / 1000000000000) (2160874028 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11195342381 / 1000000000000) (-11195337650 / 1000000000000)
      | 1 => orderedInterval (676517460 / 1000000000000) (676525306 / 1000000000000)
      | 2 => orderedInterval (2619554983 / 1000000000000) (2619555019 / 1000000000000)
      | 3 => orderedInterval (-895626507 / 1000000000000) (-895626133 / 1000000000000)
      | 4 => orderedInterval (5865104810 / 1000000000000) (5865104879 / 1000000000000)
      | 5 => orderedInterval (-1768386177 / 1000000000000) (-1768385665 / 1000000000000)
      | 6 => orderedInterval (792032978 / 1000000000000) (792033249 / 1000000000000)
      | 7 => orderedInterval (-2702424035 / 1000000000000) (-2702423996 / 1000000000000)
      | _ => orderedInterval (-8412846820 / 1000000000000) (-8412846309 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13281781868 / 1000000000000) (-13281777120 / 1000000000000)
      | 1 => orderedInterval (5806649001 / 1000000000000) (5806661314 / 1000000000000)
      | 2 => orderedInterval (10460422 / 1000000000000) (10460486 / 1000000000000)
      | 3 => orderedInterval (-8039969269 / 1000000000000) (-8039968527 / 1000000000000)
      | 4 => orderedInterval (-3993153982 / 1000000000000) (-3993153868 / 1000000000000)
      | 5 => orderedInterval (-4789392434 / 1000000000000) (-4789391718 / 1000000000000)
      | 6 => orderedInterval (-6793655336 / 1000000000000) (-6793655093 / 1000000000000)
      | 7 => orderedInterval (-936544078 / 1000000000000) (-936544039 / 1000000000000)
      | _ => orderedInterval (-8534802968 / 1000000000000) (-8534802474 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10324527931 / 1000000000000) (10324532684 / 1000000000000)
      | 1 => orderedInterval (-3729643834 / 1000000000000) (-3729624538 / 1000000000000)
      | 2 => orderedInterval (-8656323135 / 1000000000000) (-8656323020 / 1000000000000)
      | 3 => orderedInterval (2850336334 / 1000000000000) (2850337878 / 1000000000000)
      | 4 => orderedInterval (-16242360575 / 1000000000000) (-16242360383 / 1000000000000)
      | 5 => orderedInterval (1480714619 / 1000000000000) (1480715626 / 1000000000000)
      | 6 => orderedInterval (-1805430784 / 1000000000000) (-1805430565 / 1000000000000)
      | 7 => orderedInterval (3751211815 / 1000000000000) (3751211855 / 1000000000000)
      | _ => orderedInterval (12480713925 / 1000000000000) (12480714593 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (14300930262 / 1000000000000) (14300935035 / 1000000000000)
      | 1 => orderedInterval (-13242935105 / 1000000000000) (-13242904804 / 1000000000000)
      | 2 => orderedInterval (-2257621289 / 1000000000000) (-2257621075 / 1000000000000)
      | 3 => orderedInterval (55990488571 / 1000000000000) (55990491890 / 1000000000000)
      | 4 => orderedInterval (11159403838 / 1000000000000) (11159404172 / 1000000000000)
      | 5 => orderedInterval (11990624941 / 1000000000000) (11990626369 / 1000000000000)
      | 6 => orderedInterval (7138734933 / 1000000000000) (7138735132 / 1000000000000)
      | 7 => orderedInterval (698666901 / 1000000000000) (698666943 / 1000000000000)
      | _ => orderedInterval (29937455680 / 1000000000000) (29937456757 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21395381592 / 1000000000000) (21395393093 / 1000000000000)
    | 1 => orderedInterval (-15021415689 / 1000000000000) (-15021401300 / 1000000000000)
    | 2 => orderedInterval (-40552190512 / 1000000000000) (-40552171039 / 1000000000000)
    | 3 => orderedInterval (453746296 / 1000000000000) (453774130 / 1000000000000)
    | _ => orderedInterval (115715748732 / 1000000000000) (115715790419 / 1000000000000)

theorem compactCertificate482_stateChecks0 :
    compactCertificate482.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (707 / 2)) (orderedInterval (27820065828 / 1000000000000) (27820077692 / 1000000000000), orderedInterval (-32085391418 / 1000000000000) (-32085379553 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1041546000166007 / 4000000000000)) (orderedInterval (-20127224269 / 1000000000000) (-20127224268 / 1000000000000), orderedInterval (-45125507537 / 1000000000000) (-45125507536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (336814576540631 / 800000000000)) (orderedInterval (28692490085 / 1000000000000) (28692490086 / 1000000000000), orderedInterval (26211618952 / 1000000000000) (26211618953 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_stateChecks1 :
    compactCertificate482.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (303920525195749 / 4000000000000)) (orderedInterval (89615439608 / 1000000000000) (89615439609 / 1000000000000), orderedInterval (18056289805 / 1000000000000) (18056289807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (816373280633953 / 4000000000000)) (orderedInterval (-34882494051 / 1000000000000) (-34882494050 / 1000000000000), orderedInterval (-43531878325 / 1000000000000) (-43531878324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2216612264140701 / 4000000000000)) (orderedInterval (30561987046 / 1000000000000) (30562057016 / 1000000000000), orderedInterval (-14682923144 / 1000000000000) (-14682853175 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_stateChecks2 :
    compactCertificate482.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1632746561268613 / 4000000000000)) (orderedInterval (21134276844 / 1000000000000) (21134276845 / 1000000000000), orderedInterval (33335346517 / 1000000000000) (33335346518 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2797739062007449 / 4000000000000)) (orderedInterval (10491587339 / 1000000000000) (10491587354 / 1000000000000), orderedInterval (-28293866884 / 1000000000000) (-28293866869 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2060801930367691 / 4000000000000)) (orderedInterval (24330031156 / 1000000000000) (24330031157 / 1000000000000), orderedInterval (25348094011 / 1000000000000) (25348094012 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_stateChecks3 :
    compactCertificate482.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (3161800120184293 / 4000000000000)) (orderedInterval (-12243747725 / 1000000000000) (-12243747695 / 1000000000000), orderedInterval (25610083728 / 1000000000000) (25610083758 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1825466150511997 / 4000000000000)) (orderedInterval (-37302801348 / 1000000000000) (-37302800605 / 1000000000000), orderedInterval (1904977818 / 1000000000000) (1904978561 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (3239321717954273 / 4000000000000)) (orderedInterval (2373876450 / 1000000000000) (2373876451 / 1000000000000), orderedInterval (27935602272 / 1000000000000) (27935602273 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_stateChecks4 :
    compactCertificate482.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (3026594542674437 / 4000000000000)) (orderedInterval (-8849714085 / 1000000000000) (-8849714084 / 1000000000000), orderedInterval (-27617520336 / 1000000000000) (-27617520335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2159920677555221 / 4000000000000)) (orderedInterval (13730754740 / 1000000000000) (13730754741 / 1000000000000), orderedInterval (31458471403 / 1000000000000) (31458471404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2449119841901859 / 4000000000000)) (orderedInterval (-14158584059 / 1000000000000) (-14158584058 / 1000000000000), orderedInterval (-28958896228 / 1000000000000) (-28958896227 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_stateChecks5 :
    compactCertificate482.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2041820790598771 / 4000000000000)) (orderedInterval (26279531005 / 1000000000000) (26279549315 / 1000000000000), orderedInterval (-23616990307 / 1000000000000) (-23616971997 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1804010590706191 / 4000000000000)) (orderedInterval (-21262831180 / 1000000000000) (-21262829032 / 1000000000000), orderedInterval (30998688412 / 1000000000000) (30998690560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (522872583876909 / 800000000000)) (orderedInterval (24918271546 / 1000000000000) (24918271547 / 1000000000000), orderedInterval (18772263587 / 1000000000000) (18772263588 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_stateChecks6 :
    compactCertificate482.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1446293084280023 / 4000000000000)) (orderedInterval (-36911491197 / 1000000000000) (-36911491196 / 1000000000000), orderedInterval (-19904772732 / 1000000000000) (-19904772731 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1226038664801503 / 4000000000000)) (orderedInterval (-25029915664 / 1000000000000) (-25029911821 / 1000000000000), orderedInterval (38126283521 / 1000000000000) (38126287364 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (767198069632309 / 4000000000000)) (orderedInterval (-46765797734 / 1000000000000) (-46765797733 / 1000000000000), orderedInterval (-33525530227 / 1000000000000) (-33525530226 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_stateChecks7 :
    compactCertificate482.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (412601673433803 / 4000000000000)) (orderedInterval (-20351652845 / 1000000000000) (-20351652844 / 1000000000000), orderedInterval (-75780429509 / 1000000000000) (-75780429508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1120293805830409 / 4000000000000)) (orderedInterval (-45343276911 / 1000000000000) (-45343276909 / 1000000000000), orderedInterval (-14650991905 / 1000000000000) (-14650991903 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1529665414997993 / 4000000000000)) (orderedInterval (-2970897777 / 1000000000000) (-2970897775 / 1000000000000), orderedInterval (40696692581 / 1000000000000) (40696692583 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_stateChecks8 :
    compactCertificate482.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (646801930367691 / 4000000000000)) (orderedInterval (-48268866077 / 1000000000000) (-48268761576 / 1000000000000), orderedInterval (40238456791 / 1000000000000) (40238561292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2629213937575211 / 4000000000000)) (orderedInterval (-31033836058 / 1000000000000) (-31033835499 / 1000000000000), orderedInterval (-2307323882 / 1000000000000) (-2307323323 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1756193061842149 / 4000000000000)) (orderedInterval (396295222 / 1000000000000) (396295223 / 1000000000000), orderedInterval (38076357983 / 1000000000000) (38076357984 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_states : ∀ j,
    BesselStateValid (compactCertificate482.point j) (compactCertificate482.state j) :=
  compactCertificate482.statesValid_of_checks3 compactCertificate482_stateChecks0
    compactCertificate482_stateChecks1 compactCertificate482_stateChecks2
    compactCertificate482_stateChecks3 compactCertificate482_stateChecks4
    compactCertificate482_stateChecks5 compactCertificate482_stateChecks6
    compactCertificate482_stateChecks7 compactCertificate482_stateChecks8

theorem compactCertificate482_chunkChecks0_0 :
    compactCertificate482.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (707 / 2) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27820065828 / 1000000000000) (27820077692 / 1000000000000), orderedInterval (-32085391418 / 1000000000000) (-32085379553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1041546000166007 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20127224269 / 1000000000000) (-20127224268 / 1000000000000), orderedInterval (-45125507537 / 1000000000000) (-45125507536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (336814576540631 / 800000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28692490085 / 1000000000000) (28692490086 / 1000000000000), orderedInterval (26211618952 / 1000000000000) (26211618953 / 1000000000000)))) (orderedInterval (12523061529 / 1000000000000) (12523066256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (303920525195749 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89615439608 / 1000000000000) (89615439609 / 1000000000000), orderedInterval (18056289805 / 1000000000000) (18056289807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (816373280633953 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34882494051 / 1000000000000) (-34882494050 / 1000000000000), orderedInterval (-43531878325 / 1000000000000) (-43531878324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2216612264140701 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30561987046 / 1000000000000) (30562057016 / 1000000000000), orderedInterval (-14682923144 / 1000000000000) (-14682853175 / 1000000000000)))) (orderedInterval (-4418530428 / 1000000000000) (-4418525411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1632746561268613 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21134276844 / 1000000000000) (21134276845 / 1000000000000), orderedInterval (33335346517 / 1000000000000) (33335346518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2797739062007449 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10491587339 / 1000000000000) (10491587354 / 1000000000000), orderedInterval (-28293866884 / 1000000000000) (-28293866869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2060801930367691 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24330031156 / 1000000000000) (24330031157 / 1000000000000), orderedInterval (25348094011 / 1000000000000) (25348094012 / 1000000000000)))) (orderedInterval (264406309 / 1000000000000) (264406330 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks0_1 :
    compactCertificate482.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3161800120184293 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12243747725 / 1000000000000) (-12243747695 / 1000000000000), orderedInterval (25610083728 / 1000000000000) (25610083758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1825466150511997 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37302801348 / 1000000000000) (-37302800605 / 1000000000000), orderedInterval (1904977818 / 1000000000000) (1904978561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3239321717954273 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2373876450 / 1000000000000) (2373876451 / 1000000000000), orderedInterval (27935602272 / 1000000000000) (27935602273 / 1000000000000)))) (orderedInterval (-250804027 / 1000000000000) (-250803826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3026594542674437 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8849714085 / 1000000000000) (-8849714084 / 1000000000000), orderedInterval (-27617520336 / 1000000000000) (-27617520335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2159920677555221 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13730754740 / 1000000000000) (13730754741 / 1000000000000), orderedInterval (31458471403 / 1000000000000) (31458471404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2449119841901859 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14158584059 / 1000000000000) (-14158584058 / 1000000000000), orderedInterval (-28958896228 / 1000000000000) (-28958896227 / 1000000000000)))) (orderedInterval (1529834739 / 1000000000000) (1529834782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2041820790598771 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26279531005 / 1000000000000) (26279549315 / 1000000000000), orderedInterval (-23616990307 / 1000000000000) (-23616971997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1804010590706191 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21262831180 / 1000000000000) (-21262829032 / 1000000000000), orderedInterval (30998688412 / 1000000000000) (30998690560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (522872583876909 / 800000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24918271546 / 1000000000000) (24918271547 / 1000000000000), orderedInterval (18772263587 / 1000000000000) (18772263588 / 1000000000000)))) (orderedInterval (2158274562 / 1000000000000) (2158274931 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks0_2 :
    compactCertificate482.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1446293084280023 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36911491197 / 1000000000000) (-36911491196 / 1000000000000), orderedInterval (-19904772732 / 1000000000000) (-19904772731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1226038664801503 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25029915664 / 1000000000000) (-25029911821 / 1000000000000), orderedInterval (38126283521 / 1000000000000) (38126287364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (767198069632309 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46765797734 / 1000000000000) (-46765797733 / 1000000000000), orderedInterval (-33525530227 / 1000000000000) (-33525530226 / 1000000000000)))) (orderedInterval (5796087110 / 1000000000000) (5796087416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (412601673433803 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20351652845 / 1000000000000) (-20351652844 / 1000000000000), orderedInterval (-75780429509 / 1000000000000) (-75780429508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1120293805830409 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45343276911 / 1000000000000) (-45343276909 / 1000000000000), orderedInterval (-14650991905 / 1000000000000) (-14650991903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1529665414997993 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2970897777 / 1000000000000) (-2970897775 / 1000000000000), orderedInterval (40696692581 / 1000000000000) (40696692583 / 1000000000000)))) (orderedInterval (1632178544 / 1000000000000) (1632178587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (646801930367691 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-48268866077 / 1000000000000) (-48268761576 / 1000000000000), orderedInterval (40238456791 / 1000000000000) (40238561292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2629213937575211 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31033836058 / 1000000000000) (-31033835499 / 1000000000000), orderedInterval (-2307323882 / 1000000000000) (-2307323323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1756193061842149 / 4000000000000) 0 (IntervalRat.scale (707 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (396295222 / 1000000000000) (396295223 / 1000000000000), orderedInterval (38076357983 / 1000000000000) (38076357984 / 1000000000000)))) (orderedInterval (2160873254 / 1000000000000) (2160874028 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks0 :
    compactCertificate482.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate482.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate482_chunkChecks0_0
    compactCertificate482_chunkChecks0_1 compactCertificate482_chunkChecks0_2

theorem compactCertificate482_chunkChecks1_0 :
    compactCertificate482.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (707 / 2) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27820065828 / 1000000000000) (27820077692 / 1000000000000), orderedInterval (-32085391418 / 1000000000000) (-32085379553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1041546000166007 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20127224269 / 1000000000000) (-20127224268 / 1000000000000), orderedInterval (-45125507537 / 1000000000000) (-45125507536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (336814576540631 / 800000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28692490085 / 1000000000000) (28692490086 / 1000000000000), orderedInterval (26211618952 / 1000000000000) (26211618953 / 1000000000000)))) (orderedInterval (-11195342381 / 1000000000000) (-11195337650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (303920525195749 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89615439608 / 1000000000000) (89615439609 / 1000000000000), orderedInterval (18056289805 / 1000000000000) (18056289807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (816373280633953 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34882494051 / 1000000000000) (-34882494050 / 1000000000000), orderedInterval (-43531878325 / 1000000000000) (-43531878324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2216612264140701 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30561987046 / 1000000000000) (30562057016 / 1000000000000), orderedInterval (-14682923144 / 1000000000000) (-14682853175 / 1000000000000)))) (orderedInterval (676517460 / 1000000000000) (676525306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1632746561268613 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21134276844 / 1000000000000) (21134276845 / 1000000000000), orderedInterval (33335346517 / 1000000000000) (33335346518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2797739062007449 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10491587339 / 1000000000000) (10491587354 / 1000000000000), orderedInterval (-28293866884 / 1000000000000) (-28293866869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2060801930367691 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24330031156 / 1000000000000) (24330031157 / 1000000000000), orderedInterval (25348094011 / 1000000000000) (25348094012 / 1000000000000)))) (orderedInterval (2619554983 / 1000000000000) (2619555019 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks1_1 :
    compactCertificate482.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3161800120184293 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12243747725 / 1000000000000) (-12243747695 / 1000000000000), orderedInterval (25610083728 / 1000000000000) (25610083758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1825466150511997 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37302801348 / 1000000000000) (-37302800605 / 1000000000000), orderedInterval (1904977818 / 1000000000000) (1904978561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3239321717954273 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2373876450 / 1000000000000) (2373876451 / 1000000000000), orderedInterval (27935602272 / 1000000000000) (27935602273 / 1000000000000)))) (orderedInterval (-895626507 / 1000000000000) (-895626133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3026594542674437 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8849714085 / 1000000000000) (-8849714084 / 1000000000000), orderedInterval (-27617520336 / 1000000000000) (-27617520335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2159920677555221 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13730754740 / 1000000000000) (13730754741 / 1000000000000), orderedInterval (31458471403 / 1000000000000) (31458471404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2449119841901859 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14158584059 / 1000000000000) (-14158584058 / 1000000000000), orderedInterval (-28958896228 / 1000000000000) (-28958896227 / 1000000000000)))) (orderedInterval (5865104810 / 1000000000000) (5865104879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2041820790598771 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26279531005 / 1000000000000) (26279549315 / 1000000000000), orderedInterval (-23616990307 / 1000000000000) (-23616971997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1804010590706191 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21262831180 / 1000000000000) (-21262829032 / 1000000000000), orderedInterval (30998688412 / 1000000000000) (30998690560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (522872583876909 / 800000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24918271546 / 1000000000000) (24918271547 / 1000000000000), orderedInterval (18772263587 / 1000000000000) (18772263588 / 1000000000000)))) (orderedInterval (-1768386177 / 1000000000000) (-1768385665 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks1_2 :
    compactCertificate482.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1446293084280023 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36911491197 / 1000000000000) (-36911491196 / 1000000000000), orderedInterval (-19904772732 / 1000000000000) (-19904772731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1226038664801503 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25029915664 / 1000000000000) (-25029911821 / 1000000000000), orderedInterval (38126283521 / 1000000000000) (38126287364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (767198069632309 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46765797734 / 1000000000000) (-46765797733 / 1000000000000), orderedInterval (-33525530227 / 1000000000000) (-33525530226 / 1000000000000)))) (orderedInterval (792032978 / 1000000000000) (792033249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (412601673433803 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20351652845 / 1000000000000) (-20351652844 / 1000000000000), orderedInterval (-75780429509 / 1000000000000) (-75780429508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1120293805830409 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45343276911 / 1000000000000) (-45343276909 / 1000000000000), orderedInterval (-14650991905 / 1000000000000) (-14650991903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1529665414997993 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2970897777 / 1000000000000) (-2970897775 / 1000000000000), orderedInterval (40696692581 / 1000000000000) (40696692583 / 1000000000000)))) (orderedInterval (-2702424035 / 1000000000000) (-2702423996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (646801930367691 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-48268866077 / 1000000000000) (-48268761576 / 1000000000000), orderedInterval (40238456791 / 1000000000000) (40238561292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2629213937575211 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31033836058 / 1000000000000) (-31033835499 / 1000000000000), orderedInterval (-2307323882 / 1000000000000) (-2307323323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1756193061842149 / 4000000000000) 1 (IntervalRat.scale (707 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (396295222 / 1000000000000) (396295223 / 1000000000000), orderedInterval (38076357983 / 1000000000000) (38076357984 / 1000000000000)))) (orderedInterval (-8412846820 / 1000000000000) (-8412846309 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks1 :
    compactCertificate482.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate482.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate482_chunkChecks1_0
    compactCertificate482_chunkChecks1_1 compactCertificate482_chunkChecks1_2

theorem compactCertificate482_chunkChecks2_0 :
    compactCertificate482.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (707 / 2) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27820065828 / 1000000000000) (27820077692 / 1000000000000), orderedInterval (-32085391418 / 1000000000000) (-32085379553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1041546000166007 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20127224269 / 1000000000000) (-20127224268 / 1000000000000), orderedInterval (-45125507537 / 1000000000000) (-45125507536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (336814576540631 / 800000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28692490085 / 1000000000000) (28692490086 / 1000000000000), orderedInterval (26211618952 / 1000000000000) (26211618953 / 1000000000000)))) (orderedInterval (-13281781868 / 1000000000000) (-13281777120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (303920525195749 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89615439608 / 1000000000000) (89615439609 / 1000000000000), orderedInterval (18056289805 / 1000000000000) (18056289807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (816373280633953 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34882494051 / 1000000000000) (-34882494050 / 1000000000000), orderedInterval (-43531878325 / 1000000000000) (-43531878324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2216612264140701 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30561987046 / 1000000000000) (30562057016 / 1000000000000), orderedInterval (-14682923144 / 1000000000000) (-14682853175 / 1000000000000)))) (orderedInterval (5806649001 / 1000000000000) (5806661314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1632746561268613 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21134276844 / 1000000000000) (21134276845 / 1000000000000), orderedInterval (33335346517 / 1000000000000) (33335346518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2797739062007449 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10491587339 / 1000000000000) (10491587354 / 1000000000000), orderedInterval (-28293866884 / 1000000000000) (-28293866869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2060801930367691 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24330031156 / 1000000000000) (24330031157 / 1000000000000), orderedInterval (25348094011 / 1000000000000) (25348094012 / 1000000000000)))) (orderedInterval (10460422 / 1000000000000) (10460486 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks2_1 :
    compactCertificate482.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3161800120184293 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12243747725 / 1000000000000) (-12243747695 / 1000000000000), orderedInterval (25610083728 / 1000000000000) (25610083758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1825466150511997 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37302801348 / 1000000000000) (-37302800605 / 1000000000000), orderedInterval (1904977818 / 1000000000000) (1904978561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3239321717954273 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2373876450 / 1000000000000) (2373876451 / 1000000000000), orderedInterval (27935602272 / 1000000000000) (27935602273 / 1000000000000)))) (orderedInterval (-8039969269 / 1000000000000) (-8039968527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3026594542674437 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8849714085 / 1000000000000) (-8849714084 / 1000000000000), orderedInterval (-27617520336 / 1000000000000) (-27617520335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2159920677555221 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13730754740 / 1000000000000) (13730754741 / 1000000000000), orderedInterval (31458471403 / 1000000000000) (31458471404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2449119841901859 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14158584059 / 1000000000000) (-14158584058 / 1000000000000), orderedInterval (-28958896228 / 1000000000000) (-28958896227 / 1000000000000)))) (orderedInterval (-3993153982 / 1000000000000) (-3993153868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2041820790598771 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26279531005 / 1000000000000) (26279549315 / 1000000000000), orderedInterval (-23616990307 / 1000000000000) (-23616971997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1804010590706191 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21262831180 / 1000000000000) (-21262829032 / 1000000000000), orderedInterval (30998688412 / 1000000000000) (30998690560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (522872583876909 / 800000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24918271546 / 1000000000000) (24918271547 / 1000000000000), orderedInterval (18772263587 / 1000000000000) (18772263588 / 1000000000000)))) (orderedInterval (-4789392434 / 1000000000000) (-4789391718 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks2_2 :
    compactCertificate482.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1446293084280023 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36911491197 / 1000000000000) (-36911491196 / 1000000000000), orderedInterval (-19904772732 / 1000000000000) (-19904772731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1226038664801503 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25029915664 / 1000000000000) (-25029911821 / 1000000000000), orderedInterval (38126283521 / 1000000000000) (38126287364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (767198069632309 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46765797734 / 1000000000000) (-46765797733 / 1000000000000), orderedInterval (-33525530227 / 1000000000000) (-33525530226 / 1000000000000)))) (orderedInterval (-6793655336 / 1000000000000) (-6793655093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (412601673433803 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20351652845 / 1000000000000) (-20351652844 / 1000000000000), orderedInterval (-75780429509 / 1000000000000) (-75780429508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1120293805830409 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45343276911 / 1000000000000) (-45343276909 / 1000000000000), orderedInterval (-14650991905 / 1000000000000) (-14650991903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1529665414997993 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2970897777 / 1000000000000) (-2970897775 / 1000000000000), orderedInterval (40696692581 / 1000000000000) (40696692583 / 1000000000000)))) (orderedInterval (-936544078 / 1000000000000) (-936544039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (646801930367691 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-48268866077 / 1000000000000) (-48268761576 / 1000000000000), orderedInterval (40238456791 / 1000000000000) (40238561292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2629213937575211 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31033836058 / 1000000000000) (-31033835499 / 1000000000000), orderedInterval (-2307323882 / 1000000000000) (-2307323323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1756193061842149 / 4000000000000) 2 (IntervalRat.scale (707 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (396295222 / 1000000000000) (396295223 / 1000000000000), orderedInterval (38076357983 / 1000000000000) (38076357984 / 1000000000000)))) (orderedInterval (-8534802968 / 1000000000000) (-8534802474 / 1000000000000))) = true
  rfl'

theorem compactCertificate482_chunkChecks2 :
    compactCertificate482.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate482.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate482_chunkChecks2_0
    compactCertificate482_chunkChecks2_1 compactCertificate482_chunkChecks2_2

theorem compactCertificate482_chunkChecks3_0 :
    compactCertificate482.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (707 / 2) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27820065828 / 1000000000000) (27820077692 / 1000000000000), orderedInterval (-32085391418 / 1000000000000) (-32085379553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1041546000166007 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20127224269 / 1000000000000) (-20127224268 / 1000000000000), orderedInterval (-45125507537 / 1000000000000) (-45125507536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (336814576540631 / 800000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28692490085 / 1000000000000) (28692490086 / 1000000000000), orderedInterval (26211618952 / 1000000000000) (26211618953 / 1000000000000)))) (orderedInterval (10324527931 / 1000000000000) (10324532684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (303920525195749 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89615439608 / 1000000000000) (89615439609 / 1000000000000), orderedInterval (18056289805 / 1000000000000) (18056289807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (816373280633953 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34882494051 / 1000000000000) (-34882494050 / 1000000000000), orderedInterval (-43531878325 / 1000000000000) (-43531878324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2216612264140701 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30561987046 / 1000000000000) (30562057016 / 1000000000000), orderedInterval (-14682923144 / 1000000000000) (-14682853175 / 1000000000000)))) (orderedInterval (-3729643834 / 1000000000000) (-3729624538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1632746561268613 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21134276844 / 1000000000000) (21134276845 / 1000000000000), orderedInterval (33335346517 / 1000000000000) (33335346518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2797739062007449 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10491587339 / 1000000000000) (10491587354 / 1000000000000), orderedInterval (-28293866884 / 1000000000000) (-28293866869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2060801930367691 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24330031156 / 1000000000000) (24330031157 / 1000000000000), orderedInterval (25348094011 / 1000000000000) (25348094012 / 1000000000000)))) (orderedInterval (-8656323135 / 1000000000000) (-8656323020 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate482_chunkChecks3_1 :
    compactCertificate482.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3161800120184293 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12243747725 / 1000000000000) (-12243747695 / 1000000000000), orderedInterval (25610083728 / 1000000000000) (25610083758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1825466150511997 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37302801348 / 1000000000000) (-37302800605 / 1000000000000), orderedInterval (1904977818 / 1000000000000) (1904978561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3239321717954273 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2373876450 / 1000000000000) (2373876451 / 1000000000000), orderedInterval (27935602272 / 1000000000000) (27935602273 / 1000000000000)))) (orderedInterval (2850336334 / 1000000000000) (2850337878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3026594542674437 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8849714085 / 1000000000000) (-8849714084 / 1000000000000), orderedInterval (-27617520336 / 1000000000000) (-27617520335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2159920677555221 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13730754740 / 1000000000000) (13730754741 / 1000000000000), orderedInterval (31458471403 / 1000000000000) (31458471404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2449119841901859 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14158584059 / 1000000000000) (-14158584058 / 1000000000000), orderedInterval (-28958896228 / 1000000000000) (-28958896227 / 1000000000000)))) (orderedInterval (-16242360575 / 1000000000000) (-16242360383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2041820790598771 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26279531005 / 1000000000000) (26279549315 / 1000000000000), orderedInterval (-23616990307 / 1000000000000) (-23616971997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1804010590706191 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21262831180 / 1000000000000) (-21262829032 / 1000000000000), orderedInterval (30998688412 / 1000000000000) (30998690560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (522872583876909 / 800000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24918271546 / 1000000000000) (24918271547 / 1000000000000), orderedInterval (18772263587 / 1000000000000) (18772263588 / 1000000000000)))) (orderedInterval (1480714619 / 1000000000000) (1480715626 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate482_chunkChecks3_2 :
    compactCertificate482.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1446293084280023 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36911491197 / 1000000000000) (-36911491196 / 1000000000000), orderedInterval (-19904772732 / 1000000000000) (-19904772731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1226038664801503 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25029915664 / 1000000000000) (-25029911821 / 1000000000000), orderedInterval (38126283521 / 1000000000000) (38126287364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (767198069632309 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46765797734 / 1000000000000) (-46765797733 / 1000000000000), orderedInterval (-33525530227 / 1000000000000) (-33525530226 / 1000000000000)))) (orderedInterval (-1805430784 / 1000000000000) (-1805430565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (412601673433803 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20351652845 / 1000000000000) (-20351652844 / 1000000000000), orderedInterval (-75780429509 / 1000000000000) (-75780429508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1120293805830409 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45343276911 / 1000000000000) (-45343276909 / 1000000000000), orderedInterval (-14650991905 / 1000000000000) (-14650991903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1529665414997993 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2970897777 / 1000000000000) (-2970897775 / 1000000000000), orderedInterval (40696692581 / 1000000000000) (40696692583 / 1000000000000)))) (orderedInterval (3751211815 / 1000000000000) (3751211855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (646801930367691 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-48268866077 / 1000000000000) (-48268761576 / 1000000000000), orderedInterval (40238456791 / 1000000000000) (40238561292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2629213937575211 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31033836058 / 1000000000000) (-31033835499 / 1000000000000), orderedInterval (-2307323882 / 1000000000000) (-2307323323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1756193061842149 / 4000000000000) 3 (IntervalRat.scale (707 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (396295222 / 1000000000000) (396295223 / 1000000000000), orderedInterval (38076357983 / 1000000000000) (38076357984 / 1000000000000)))) (orderedInterval (12480713925 / 1000000000000) (12480714593 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate482_chunkChecks3 :
    compactCertificate482.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate482.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate482_chunkChecks3_0
    compactCertificate482_chunkChecks3_1 compactCertificate482_chunkChecks3_2

theorem compactCertificate482_chunkChecks4_0 :
    compactCertificate482.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (707 / 2) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27820065828 / 1000000000000) (27820077692 / 1000000000000), orderedInterval (-32085391418 / 1000000000000) (-32085379553 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1041546000166007 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-20127224269 / 1000000000000) (-20127224268 / 1000000000000), orderedInterval (-45125507537 / 1000000000000) (-45125507536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (336814576540631 / 800000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28692490085 / 1000000000000) (28692490086 / 1000000000000), orderedInterval (26211618952 / 1000000000000) (26211618953 / 1000000000000)))) (orderedInterval (14300930262 / 1000000000000) (14300935035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (303920525195749 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89615439608 / 1000000000000) (89615439609 / 1000000000000), orderedInterval (18056289805 / 1000000000000) (18056289807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (816373280633953 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34882494051 / 1000000000000) (-34882494050 / 1000000000000), orderedInterval (-43531878325 / 1000000000000) (-43531878324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2216612264140701 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30561987046 / 1000000000000) (30562057016 / 1000000000000), orderedInterval (-14682923144 / 1000000000000) (-14682853175 / 1000000000000)))) (orderedInterval (-13242935105 / 1000000000000) (-13242904804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1632746561268613 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21134276844 / 1000000000000) (21134276845 / 1000000000000), orderedInterval (33335346517 / 1000000000000) (33335346518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2797739062007449 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10491587339 / 1000000000000) (10491587354 / 1000000000000), orderedInterval (-28293866884 / 1000000000000) (-28293866869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2060801930367691 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24330031156 / 1000000000000) (24330031157 / 1000000000000), orderedInterval (25348094011 / 1000000000000) (25348094012 / 1000000000000)))) (orderedInterval (-2257621289 / 1000000000000) (-2257621075 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate482_chunkChecks4_1 :
    compactCertificate482.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3161800120184293 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12243747725 / 1000000000000) (-12243747695 / 1000000000000), orderedInterval (25610083728 / 1000000000000) (25610083758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1825466150511997 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37302801348 / 1000000000000) (-37302800605 / 1000000000000), orderedInterval (1904977818 / 1000000000000) (1904978561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3239321717954273 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2373876450 / 1000000000000) (2373876451 / 1000000000000), orderedInterval (27935602272 / 1000000000000) (27935602273 / 1000000000000)))) (orderedInterval (55990488571 / 1000000000000) (55990491890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3026594542674437 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8849714085 / 1000000000000) (-8849714084 / 1000000000000), orderedInterval (-27617520336 / 1000000000000) (-27617520335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2159920677555221 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13730754740 / 1000000000000) (13730754741 / 1000000000000), orderedInterval (31458471403 / 1000000000000) (31458471404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2449119841901859 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14158584059 / 1000000000000) (-14158584058 / 1000000000000), orderedInterval (-28958896228 / 1000000000000) (-28958896227 / 1000000000000)))) (orderedInterval (11159403838 / 1000000000000) (11159404172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2041820790598771 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26279531005 / 1000000000000) (26279549315 / 1000000000000), orderedInterval (-23616990307 / 1000000000000) (-23616971997 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1804010590706191 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21262831180 / 1000000000000) (-21262829032 / 1000000000000), orderedInterval (30998688412 / 1000000000000) (30998690560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (522872583876909 / 800000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24918271546 / 1000000000000) (24918271547 / 1000000000000), orderedInterval (18772263587 / 1000000000000) (18772263588 / 1000000000000)))) (orderedInterval (11990624941 / 1000000000000) (11990626369 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate482_chunkChecks4_2 :
    compactCertificate482.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1446293084280023 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36911491197 / 1000000000000) (-36911491196 / 1000000000000), orderedInterval (-19904772732 / 1000000000000) (-19904772731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1226038664801503 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25029915664 / 1000000000000) (-25029911821 / 1000000000000), orderedInterval (38126283521 / 1000000000000) (38126287364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (767198069632309 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46765797734 / 1000000000000) (-46765797733 / 1000000000000), orderedInterval (-33525530227 / 1000000000000) (-33525530226 / 1000000000000)))) (orderedInterval (7138734933 / 1000000000000) (7138735132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (412601673433803 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20351652845 / 1000000000000) (-20351652844 / 1000000000000), orderedInterval (-75780429509 / 1000000000000) (-75780429508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1120293805830409 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45343276911 / 1000000000000) (-45343276909 / 1000000000000), orderedInterval (-14650991905 / 1000000000000) (-14650991903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1529665414997993 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2970897777 / 1000000000000) (-2970897775 / 1000000000000), orderedInterval (40696692581 / 1000000000000) (40696692583 / 1000000000000)))) (orderedInterval (698666901 / 1000000000000) (698666943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (646801930367691 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-48268866077 / 1000000000000) (-48268761576 / 1000000000000), orderedInterval (40238456791 / 1000000000000) (40238561292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2629213937575211 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31033836058 / 1000000000000) (-31033835499 / 1000000000000), orderedInterval (-2307323882 / 1000000000000) (-2307323323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1756193061842149 / 4000000000000) 4 (IntervalRat.scale (707 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (396295222 / 1000000000000) (396295223 / 1000000000000), orderedInterval (38076357983 / 1000000000000) (38076357984 / 1000000000000)))) (orderedInterval (29937455680 / 1000000000000) (29937456757 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate482_chunkChecks4 :
    compactCertificate482.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate482.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate482_chunkChecks4_0
    compactCertificate482_chunkChecks4_1 compactCertificate482_chunkChecks4_2

theorem compactCertificate482_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate482.chunkCheck r b = true :=
  compactCertificate482.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate482_chunkChecks0
    · exact compactCertificate482_chunkChecks1
    · exact compactCertificate482_chunkChecks2
    · exact compactCertificate482_chunkChecks3
    · exact compactCertificate482_chunkChecks4)

theorem compactCertificate482_coefficient0 :
    compactCertificate482.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate482_coefficient1 :
    compactCertificate482.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate482_coefficient2 :
    compactCertificate482.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate482_coefficient3 :
    compactCertificate482.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate482_coefficient4 :
    compactCertificate482.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate482_coefficients : ∀ r : Fin 5,
    compactCertificate482.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate482_coefficient0
  · exact compactCertificate482_coefficient1
  · exact compactCertificate482_coefficient2
  · exact compactCertificate482_coefficient3
  · exact compactCertificate482_coefficient4

theorem compactCertificate482_lower : (1 : ℚ) ≤ compactCertificate482.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate482, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate482_proves {t : ℝ} (ht : t ∈ compactCertificate482.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate482.proves compactCertificate482_states compactCertificate482_chunks
    compactCertificate482_coefficients compactCertificate482_lower ht

end Erdos232
