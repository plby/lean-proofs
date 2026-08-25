/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate527 : CompactCertificate where
  left := 398
  right := 399
  center := 797 / 2
  grid := fun i =>
    match i.val with
    | 0 => 127
    | 1 => 93
    | 2 => 151
    | 3 => 27
    | 4 => 73
    | 5 => 199
    | 6 => 147
    | 7 => 251
    | 8 => 185
    | 9 => 284
    | 10 => 164
    | 11 => 291
    | 12 => 272
    | 13 => 194
    | 14 => 220
    | 15 => 183
    | 16 => 162
    | 17 => 235
    | 18 => 130
    | 19 => 110
    | 20 => 69
    | 21 => 37
    | 22 => 101
    | 23 => 137
    | 24 => 58
    | 25 => 236
    | _ => 158
  point := fun i =>
    match i.val with
    | 0 => 797 / 2
    | 1 => 1174133185477097 / 4000000000000
    | 2 => 379690548094601 / 800000000000
    | 3 => 342609135192379 / 4000000000000
    | 4 => 920296329088063 / 4000000000000
    | 5 => 2498783556605571 / 4000000000000
    | 6 => 1840592658176923 / 4000000000000
    | 7 => 3153886891683079 / 4000000000000
    | 8 => 2323138809763861 / 4000000000000
    | 9 => 3564292356134203 / 4000000000000
    | 10 => 2057845151284387 / 4000000000000
    | 11 => 3651682332686783 / 4000000000000
    | 12 => 3411875318969627 / 4000000000000
    | 13 => 2434875219252491 / 4000000000000
    | 14 => 2760888987264189 / 4000000000000
    | 15 => 2301741400434541 / 4000000000000
    | 16 => 2033658332097361 / 4000000000000
    | 17 => 589433450282739 / 800000000000
    | 18 => 1630403943665033 / 4000000000000
    | 19 => 1382111479274113 / 4000000000000
    | 20 => 864861190236139 / 4000000000000
    | 21 => 465125224507413 / 4000000000000
    | 22 => 1262905464281239 / 4000000000000
    | 23 => 1724389442366903 / 4000000000000
    | 24 => 729138809763861 / 4000000000000
    | 25 => 2963908781113781 / 4000000000000
    | _ => 1979753706206779 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-11919249524 / 1000000000000) (-11919249523 / 1000000000000), orderedInterval (-38135703214 / 1000000000000) (-38135703213 / 1000000000000))
    | 1 => (orderedInterval (-38970970740 / 1000000000000) (-38970900632 / 1000000000000), orderedInterval (25563032823 / 1000000000000) (25563102932 / 1000000000000))
    | 2 => (orderedInterval (-31166227827 / 1000000000000) (-31166227826 / 1000000000000), orderedInterval (-19202820665 / 1000000000000) (-19202820664 / 1000000000000))
    | 3 => (orderedInterval (-86134262191 / 1000000000000) (-86134262135 / 1000000000000), orderedInterval (4159273076 / 1000000000000) (4159273131 / 1000000000000))
    | 4 => (orderedInterval (-52541520048 / 1000000000000) (-52541520006 / 1000000000000), orderedInterval (-2416226621 / 1000000000000) (-2416226578 / 1000000000000))
    | 5 => (orderedInterval (-9560390944 / 1000000000000) (-9560390943 / 1000000000000), orderedInterval (-30450297565 / 1000000000000) (-30450297564 / 1000000000000))
    | 6 => (orderedInterval (28687682837 / 1000000000000) (28687716985 / 1000000000000), orderedInterval (-23706621180 / 1000000000000) (-23706587032 / 1000000000000))
    | 7 => (orderedInterval (-18676635815 / 1000000000000) (-18676635814 / 1000000000000), orderedInterval (-21402942606 / 1000000000000) (-21402942605 / 1000000000000))
    | 8 => (orderedInterval (-12134066446 / 1000000000000) (-12134066445 / 1000000000000), orderedInterval (-30793807065 / 1000000000000) (-30793807064 / 1000000000000))
    | 9 => (orderedInterval (-9264854975 / 1000000000000) (-9264854972 / 1000000000000), orderedInterval (25077180028 / 1000000000000) (25077180031 / 1000000000000))
    | 10 => (orderedInterval (888058172 / 1000000000000) (888058173 / 1000000000000), orderedInterval (35165331744 / 1000000000000) (35165331745 / 1000000000000))
    | 11 => (orderedInterval (12605077603 / 1000000000000) (12605077628 / 1000000000000), orderedInterval (-23211561964 / 1000000000000) (-23211561938 / 1000000000000))
    | 12 => (orderedInterval (-18803595307 / 1000000000000) (-18803594042 / 1000000000000), orderedInterval (19829761360 / 1000000000000) (19829762625 / 1000000000000))
    | 13 => (orderedInterval (1132384954 / 1000000000000) (1132384955 / 1000000000000), orderedInterval (32318624572 / 1000000000000) (32318624573 / 1000000000000))
    | 14 => (orderedInterval (-4325723613 / 1000000000000) (-4325723612 / 1000000000000), orderedInterval (30063549665 / 1000000000000) (30063549667 / 1000000000000))
    | 15 => (orderedInterval (-32128808669 / 1000000000000) (-32128808646 / 1000000000000), orderedInterval (-8578271537 / 1000000000000) (-8578271513 / 1000000000000))
    | 16 => (orderedInterval (9156032415 / 1000000000000) (9156032416 / 1000000000000), orderedInterval (34171899825 / 1000000000000) (34171899826 / 1000000000000))
    | 17 => (orderedInterval (18874225185 / 1000000000000) (18874226407 / 1000000000000), orderedInterval (-22547373236 / 1000000000000) (-22547372014 / 1000000000000))
    | 18 => (orderedInterval (-828587404 / 1000000000000) (-828587402 / 1000000000000), orderedInterval (39512845878 / 1000000000000) (39512845879 / 1000000000000))
    | 19 => (orderedInterval (28870481472 / 1000000000000) (28870481473 / 1000000000000), orderedInterval (31722213708 / 1000000000000) (31722213709 / 1000000000000))
    | 20 => (orderedInterval (-12382390838 / 1000000000000) (-12382390837 / 1000000000000), orderedInterval (-52801872159 / 1000000000000) (-52801872158 / 1000000000000))
    | 21 => (orderedInterval (-54435784351 / 1000000000000) (-54435784350 / 1000000000000), orderedInterval (-49881461029 / 1000000000000) (-49881461028 / 1000000000000))
    | 22 => (orderedInterval (31881506715 / 1000000000000) (31881535631 / 1000000000000), orderedInterval (-31672238036 / 1000000000000) (-31672209120 / 1000000000000))
    | 23 => (orderedInterval (-38284648168 / 1000000000000) (-38284648063 / 1000000000000), orderedInterval (-3276317690 / 1000000000000) (-3276317584 / 1000000000000))
    | 24 => (orderedInterval (44671800353 / 1000000000000) (44671800354 / 1000000000000), orderedInterval (38566949411 / 1000000000000) (38566949412 / 1000000000000))
    | 25 => (orderedInterval (9956019614 / 1000000000000) (9956019615 / 1000000000000), orderedInterval (27562109524 / 1000000000000) (27562109525 / 1000000000000))
    | _ => (orderedInterval (-21649461656 / 1000000000000) (-21649458845 / 1000000000000), orderedInterval (28614903462 / 1000000000000) (28614906273 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-6916376890 / 1000000000000) (-6916376208 / 1000000000000)
      | 1 => orderedInterval (-304242224 / 1000000000000) (-304242173 / 1000000000000)
      | 2 => orderedInterval (282805717 / 1000000000000) (282805740 / 1000000000000)
      | 3 => orderedInterval (3503936639 / 1000000000000) (3503936801 / 1000000000000)
      | 4 => orderedInterval (468435096 / 1000000000000) (468435167 / 1000000000000)
      | 5 => orderedInterval (-411727491 / 1000000000000) (-411727421 / 1000000000000)
      | 6 => orderedInterval (-1904695257 / 1000000000000) (-1904695157 / 1000000000000)
      | 7 => orderedInterval (3215963270 / 1000000000000) (3215963982 / 1000000000000)
      | _ => orderedInterval (3520871296 / 1000000000000) (3520871934 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-16282271886 / 1000000000000) (-16282271373 / 1000000000000)
      | 1 => orderedInterval (3332791148 / 1000000000000) (3332791204 / 1000000000000)
      | 2 => orderedInterval (221522355 / 1000000000000) (221522394 / 1000000000000)
      | 3 => orderedInterval (-14159252320 / 1000000000000) (-14159251983 / 1000000000000)
      | 4 => orderedInterval (3638565505 / 1000000000000) (3638565631 / 1000000000000)
      | 5 => orderedInterval (-3705346470 / 1000000000000) (-3705346356 / 1000000000000)
      | 6 => orderedInterval (-8951569160 / 1000000000000) (-8951569067 / 1000000000000)
      | 7 => orderedInterval (1109690083 / 1000000000000) (1109690655 / 1000000000000)
      | _ => orderedInterval (-10733657180 / 1000000000000) (-10733656369 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (7556471950 / 1000000000000) (7556472342 / 1000000000000)
      | 1 => orderedInterval (-1082251597 / 1000000000000) (-1082251520 / 1000000000000)
      | 2 => orderedInterval (-1632851165 / 1000000000000) (-1632851095 / 1000000000000)
      | 3 => orderedInterval (-17709550386 / 1000000000000) (-17709549663 / 1000000000000)
      | 4 => orderedInterval (-1879916138 / 1000000000000) (-1879915905 / 1000000000000)
      | 5 => orderedInterval (-16207502 / 1000000000000) (-16207312 / 1000000000000)
      | 6 => orderedInterval (1231040688 / 1000000000000) (1231040777 / 1000000000000)
      | 7 => orderedInterval (-3068089943 / 1000000000000) (-3068089477 / 1000000000000)
      | _ => orderedInterval (-3493334773 / 1000000000000) (-3493333728 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (16905092963 / 1000000000000) (16905093267 / 1000000000000)
      | 1 => orderedInterval (-8318930335 / 1000000000000) (-8318930222 / 1000000000000)
      | 2 => orderedInterval (-2805485358 / 1000000000000) (-2805485231 / 1000000000000)
      | 3 => orderedInterval (83928824302 / 1000000000000) (83928825890 / 1000000000000)
      | 4 => orderedInterval (-6586884508 / 1000000000000) (-6586884067 / 1000000000000)
      | 5 => orderedInterval (8008133118 / 1000000000000) (8008133444 / 1000000000000)
      | 6 => orderedInterval (8202471483 / 1000000000000) (8202471570 / 1000000000000)
      | 7 => orderedInterval (-690423409 / 1000000000000) (-690423027 / 1000000000000)
      | _ => orderedInterval (24696322134 / 1000000000000) (24696323500 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8595908153 / 1000000000000) (-8595907909 / 1000000000000)
      | 1 => orderedInterval (3934924429 / 1000000000000) (3934924604 / 1000000000000)
      | 2 => orderedInterval (7519739905 / 1000000000000) (7519740138 / 1000000000000)
      | 3 => orderedInterval (90272520811 / 1000000000000) (90272524337 / 1000000000000)
      | 4 => orderedInterval (7938501346 / 1000000000000) (7938502203 / 1000000000000)
      | 5 => orderedInterval (2605780865 / 1000000000000) (2605781434 / 1000000000000)
      | 6 => orderedInterval (-854696152 / 1000000000000) (-854696067 / 1000000000000)
      | 7 => orderedInterval (3744214568 / 1000000000000) (3744214885 / 1000000000000)
      | _ => orderedInterval (-134304405 / 1000000000000) (-134302577 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (1454970156 / 1000000000000) (1454972665 / 1000000000000)
    | 1 => orderedInterval (-45529527925 / 1000000000000) (-45529525264 / 1000000000000)
    | 2 => orderedInterval (-20094688866 / 1000000000000) (-20094685581 / 1000000000000)
    | 3 => orderedInterval (123339120390 / 1000000000000) (123339125124 / 1000000000000)
    | _ => orderedInterval (106430773214 / 1000000000000) (106430781048 / 1000000000000)

theorem compactCertificate527_stateChecks0 :
    compactCertificate527.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (797 / 2)) (orderedInterval (-11919249524 / 1000000000000) (-11919249523 / 1000000000000), orderedInterval (-38135703214 / 1000000000000) (-38135703213 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1174133185477097 / 4000000000000)) (orderedInterval (-38970970740 / 1000000000000) (-38970900632 / 1000000000000), orderedInterval (25563032823 / 1000000000000) (25563102932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (379690548094601 / 800000000000)) (orderedInterval (-31166227827 / 1000000000000) (-31166227826 / 1000000000000), orderedInterval (-19202820665 / 1000000000000) (-19202820664 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_stateChecks1 :
    compactCertificate527.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (342609135192379 / 4000000000000)) (orderedInterval (-86134262191 / 1000000000000) (-86134262135 / 1000000000000), orderedInterval (4159273076 / 1000000000000) (4159273131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (920296329088063 / 4000000000000)) (orderedInterval (-52541520048 / 1000000000000) (-52541520006 / 1000000000000), orderedInterval (-2416226621 / 1000000000000) (-2416226578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2498783556605571 / 4000000000000)) (orderedInterval (-9560390944 / 1000000000000) (-9560390943 / 1000000000000), orderedInterval (-30450297565 / 1000000000000) (-30450297564 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_stateChecks2 :
    compactCertificate527.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1840592658176923 / 4000000000000)) (orderedInterval (28687682837 / 1000000000000) (28687716985 / 1000000000000), orderedInterval (-23706621180 / 1000000000000) (-23706587032 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (3153886891683079 / 4000000000000)) (orderedInterval (-18676635815 / 1000000000000) (-18676635814 / 1000000000000), orderedInterval (-21402942606 / 1000000000000) (-21402942605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2323138809763861 / 4000000000000)) (orderedInterval (-12134066446 / 1000000000000) (-12134066445 / 1000000000000), orderedInterval (-30793807065 / 1000000000000) (-30793807064 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_stateChecks3 :
    compactCertificate527.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 284 12 (3564292356134203 / 4000000000000)) (orderedInterval (-9264854975 / 1000000000000) (-9264854972 / 1000000000000), orderedInterval (25077180028 / 1000000000000) (25077180031 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2057845151284387 / 4000000000000)) (orderedInterval (888058172 / 1000000000000) (888058173 / 1000000000000), orderedInterval (35165331744 / 1000000000000) (35165331745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (3651682332686783 / 4000000000000)) (orderedInterval (12605077603 / 1000000000000) (12605077628 / 1000000000000), orderedInterval (-23211561964 / 1000000000000) (-23211561938 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_stateChecks4 :
    compactCertificate527.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (3411875318969627 / 4000000000000)) (orderedInterval (-18803595307 / 1000000000000) (-18803594042 / 1000000000000), orderedInterval (19829761360 / 1000000000000) (19829762625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2434875219252491 / 4000000000000)) (orderedInterval (1132384954 / 1000000000000) (1132384955 / 1000000000000), orderedInterval (32318624572 / 1000000000000) (32318624573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2760888987264189 / 4000000000000)) (orderedInterval (-4325723613 / 1000000000000) (-4325723612 / 1000000000000), orderedInterval (30063549665 / 1000000000000) (30063549667 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_stateChecks5 :
    compactCertificate527.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2301741400434541 / 4000000000000)) (orderedInterval (-32128808669 / 1000000000000) (-32128808646 / 1000000000000), orderedInterval (-8578271537 / 1000000000000) (-8578271513 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2033658332097361 / 4000000000000)) (orderedInterval (9156032415 / 1000000000000) (9156032416 / 1000000000000), orderedInterval (34171899825 / 1000000000000) (34171899826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (589433450282739 / 800000000000)) (orderedInterval (18874225185 / 1000000000000) (18874226407 / 1000000000000), orderedInterval (-22547373236 / 1000000000000) (-22547372014 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_stateChecks6 :
    compactCertificate527.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1630403943665033 / 4000000000000)) (orderedInterval (-828587404 / 1000000000000) (-828587402 / 1000000000000), orderedInterval (39512845878 / 1000000000000) (39512845879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1382111479274113 / 4000000000000)) (orderedInterval (28870481472 / 1000000000000) (28870481473 / 1000000000000), orderedInterval (31722213708 / 1000000000000) (31722213709 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (864861190236139 / 4000000000000)) (orderedInterval (-12382390838 / 1000000000000) (-12382390837 / 1000000000000), orderedInterval (-52801872159 / 1000000000000) (-52801872158 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_stateChecks7 :
    compactCertificate527.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (465125224507413 / 4000000000000)) (orderedInterval (-54435784351 / 1000000000000) (-54435784350 / 1000000000000), orderedInterval (-49881461029 / 1000000000000) (-49881461028 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1262905464281239 / 4000000000000)) (orderedInterval (31881506715 / 1000000000000) (31881535631 / 1000000000000), orderedInterval (-31672238036 / 1000000000000) (-31672209120 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1724389442366903 / 4000000000000)) (orderedInterval (-38284648168 / 1000000000000) (-38284648063 / 1000000000000), orderedInterval (-3276317690 / 1000000000000) (-3276317584 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_stateChecks8 :
    compactCertificate527.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (729138809763861 / 4000000000000)) (orderedInterval (44671800353 / 1000000000000) (44671800354 / 1000000000000), orderedInterval (38566949411 / 1000000000000) (38566949412 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2963908781113781 / 4000000000000)) (orderedInterval (9956019614 / 1000000000000) (9956019615 / 1000000000000), orderedInterval (27562109524 / 1000000000000) (27562109525 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1979753706206779 / 4000000000000)) (orderedInterval (-21649461656 / 1000000000000) (-21649458845 / 1000000000000), orderedInterval (28614903462 / 1000000000000) (28614906273 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_states : ∀ j,
    BesselStateValid (compactCertificate527.point j) (compactCertificate527.state j) :=
  compactCertificate527.statesValid_of_checks3 compactCertificate527_stateChecks0
    compactCertificate527_stateChecks1 compactCertificate527_stateChecks2
    compactCertificate527_stateChecks3 compactCertificate527_stateChecks4
    compactCertificate527_stateChecks5 compactCertificate527_stateChecks6
    compactCertificate527_stateChecks7 compactCertificate527_stateChecks8

theorem compactCertificate527_chunkChecks0_0 :
    compactCertificate527.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (797 / 2) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11919249524 / 1000000000000) (-11919249523 / 1000000000000), orderedInterval (-38135703214 / 1000000000000) (-38135703213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1174133185477097 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38970970740 / 1000000000000) (-38970900632 / 1000000000000), orderedInterval (25563032823 / 1000000000000) (25563102932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (379690548094601 / 800000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31166227827 / 1000000000000) (-31166227826 / 1000000000000), orderedInterval (-19202820665 / 1000000000000) (-19202820664 / 1000000000000)))) (orderedInterval (-6916376890 / 1000000000000) (-6916376208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (342609135192379 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86134262191 / 1000000000000) (-86134262135 / 1000000000000), orderedInterval (4159273076 / 1000000000000) (4159273131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (920296329088063 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52541520048 / 1000000000000) (-52541520006 / 1000000000000), orderedInterval (-2416226621 / 1000000000000) (-2416226578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2498783556605571 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9560390944 / 1000000000000) (-9560390943 / 1000000000000), orderedInterval (-30450297565 / 1000000000000) (-30450297564 / 1000000000000)))) (orderedInterval (-304242224 / 1000000000000) (-304242173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1840592658176923 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28687682837 / 1000000000000) (28687716985 / 1000000000000), orderedInterval (-23706621180 / 1000000000000) (-23706587032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3153886891683079 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18676635815 / 1000000000000) (-18676635814 / 1000000000000), orderedInterval (-21402942606 / 1000000000000) (-21402942605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2323138809763861 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12134066446 / 1000000000000) (-12134066445 / 1000000000000), orderedInterval (-30793807065 / 1000000000000) (-30793807064 / 1000000000000)))) (orderedInterval (282805717 / 1000000000000) (282805740 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks0_1 :
    compactCertificate527.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3564292356134203 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9264854975 / 1000000000000) (-9264854972 / 1000000000000), orderedInterval (25077180028 / 1000000000000) (25077180031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2057845151284387 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (888058172 / 1000000000000) (888058173 / 1000000000000), orderedInterval (35165331744 / 1000000000000) (35165331745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3651682332686783 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12605077603 / 1000000000000) (12605077628 / 1000000000000), orderedInterval (-23211561964 / 1000000000000) (-23211561938 / 1000000000000)))) (orderedInterval (3503936639 / 1000000000000) (3503936801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3411875318969627 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18803595307 / 1000000000000) (-18803594042 / 1000000000000), orderedInterval (19829761360 / 1000000000000) (19829762625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2434875219252491 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1132384954 / 1000000000000) (1132384955 / 1000000000000), orderedInterval (32318624572 / 1000000000000) (32318624573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2760888987264189 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4325723613 / 1000000000000) (-4325723612 / 1000000000000), orderedInterval (30063549665 / 1000000000000) (30063549667 / 1000000000000)))) (orderedInterval (468435096 / 1000000000000) (468435167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2301741400434541 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32128808669 / 1000000000000) (-32128808646 / 1000000000000), orderedInterval (-8578271537 / 1000000000000) (-8578271513 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2033658332097361 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9156032415 / 1000000000000) (9156032416 / 1000000000000), orderedInterval (34171899825 / 1000000000000) (34171899826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (589433450282739 / 800000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18874225185 / 1000000000000) (18874226407 / 1000000000000), orderedInterval (-22547373236 / 1000000000000) (-22547372014 / 1000000000000)))) (orderedInterval (-411727491 / 1000000000000) (-411727421 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks0_2 :
    compactCertificate527.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1630403943665033 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-828587404 / 1000000000000) (-828587402 / 1000000000000), orderedInterval (39512845878 / 1000000000000) (39512845879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1382111479274113 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28870481472 / 1000000000000) (28870481473 / 1000000000000), orderedInterval (31722213708 / 1000000000000) (31722213709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (864861190236139 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12382390838 / 1000000000000) (-12382390837 / 1000000000000), orderedInterval (-52801872159 / 1000000000000) (-52801872158 / 1000000000000)))) (orderedInterval (-1904695257 / 1000000000000) (-1904695157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (465125224507413 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-54435784351 / 1000000000000) (-54435784350 / 1000000000000), orderedInterval (-49881461029 / 1000000000000) (-49881461028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1262905464281239 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31881506715 / 1000000000000) (31881535631 / 1000000000000), orderedInterval (-31672238036 / 1000000000000) (-31672209120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1724389442366903 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38284648168 / 1000000000000) (-38284648063 / 1000000000000), orderedInterval (-3276317690 / 1000000000000) (-3276317584 / 1000000000000)))) (orderedInterval (3215963270 / 1000000000000) (3215963982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (729138809763861 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44671800353 / 1000000000000) (44671800354 / 1000000000000), orderedInterval (38566949411 / 1000000000000) (38566949412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2963908781113781 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9956019614 / 1000000000000) (9956019615 / 1000000000000), orderedInterval (27562109524 / 1000000000000) (27562109525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1979753706206779 / 4000000000000) 0 (IntervalRat.scale (797 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21649461656 / 1000000000000) (-21649458845 / 1000000000000), orderedInterval (28614903462 / 1000000000000) (28614906273 / 1000000000000)))) (orderedInterval (3520871296 / 1000000000000) (3520871934 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks0 :
    compactCertificate527.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate527.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate527_chunkChecks0_0
    compactCertificate527_chunkChecks0_1 compactCertificate527_chunkChecks0_2

theorem compactCertificate527_chunkChecks1_0 :
    compactCertificate527.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (797 / 2) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11919249524 / 1000000000000) (-11919249523 / 1000000000000), orderedInterval (-38135703214 / 1000000000000) (-38135703213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1174133185477097 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38970970740 / 1000000000000) (-38970900632 / 1000000000000), orderedInterval (25563032823 / 1000000000000) (25563102932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (379690548094601 / 800000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31166227827 / 1000000000000) (-31166227826 / 1000000000000), orderedInterval (-19202820665 / 1000000000000) (-19202820664 / 1000000000000)))) (orderedInterval (-16282271886 / 1000000000000) (-16282271373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (342609135192379 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86134262191 / 1000000000000) (-86134262135 / 1000000000000), orderedInterval (4159273076 / 1000000000000) (4159273131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (920296329088063 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52541520048 / 1000000000000) (-52541520006 / 1000000000000), orderedInterval (-2416226621 / 1000000000000) (-2416226578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2498783556605571 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9560390944 / 1000000000000) (-9560390943 / 1000000000000), orderedInterval (-30450297565 / 1000000000000) (-30450297564 / 1000000000000)))) (orderedInterval (3332791148 / 1000000000000) (3332791204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1840592658176923 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28687682837 / 1000000000000) (28687716985 / 1000000000000), orderedInterval (-23706621180 / 1000000000000) (-23706587032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3153886891683079 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18676635815 / 1000000000000) (-18676635814 / 1000000000000), orderedInterval (-21402942606 / 1000000000000) (-21402942605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2323138809763861 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12134066446 / 1000000000000) (-12134066445 / 1000000000000), orderedInterval (-30793807065 / 1000000000000) (-30793807064 / 1000000000000)))) (orderedInterval (221522355 / 1000000000000) (221522394 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks1_1 :
    compactCertificate527.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3564292356134203 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9264854975 / 1000000000000) (-9264854972 / 1000000000000), orderedInterval (25077180028 / 1000000000000) (25077180031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2057845151284387 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (888058172 / 1000000000000) (888058173 / 1000000000000), orderedInterval (35165331744 / 1000000000000) (35165331745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3651682332686783 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12605077603 / 1000000000000) (12605077628 / 1000000000000), orderedInterval (-23211561964 / 1000000000000) (-23211561938 / 1000000000000)))) (orderedInterval (-14159252320 / 1000000000000) (-14159251983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3411875318969627 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18803595307 / 1000000000000) (-18803594042 / 1000000000000), orderedInterval (19829761360 / 1000000000000) (19829762625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2434875219252491 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1132384954 / 1000000000000) (1132384955 / 1000000000000), orderedInterval (32318624572 / 1000000000000) (32318624573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2760888987264189 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4325723613 / 1000000000000) (-4325723612 / 1000000000000), orderedInterval (30063549665 / 1000000000000) (30063549667 / 1000000000000)))) (orderedInterval (3638565505 / 1000000000000) (3638565631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2301741400434541 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32128808669 / 1000000000000) (-32128808646 / 1000000000000), orderedInterval (-8578271537 / 1000000000000) (-8578271513 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2033658332097361 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9156032415 / 1000000000000) (9156032416 / 1000000000000), orderedInterval (34171899825 / 1000000000000) (34171899826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (589433450282739 / 800000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18874225185 / 1000000000000) (18874226407 / 1000000000000), orderedInterval (-22547373236 / 1000000000000) (-22547372014 / 1000000000000)))) (orderedInterval (-3705346470 / 1000000000000) (-3705346356 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks1_2 :
    compactCertificate527.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1630403943665033 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-828587404 / 1000000000000) (-828587402 / 1000000000000), orderedInterval (39512845878 / 1000000000000) (39512845879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1382111479274113 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28870481472 / 1000000000000) (28870481473 / 1000000000000), orderedInterval (31722213708 / 1000000000000) (31722213709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (864861190236139 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12382390838 / 1000000000000) (-12382390837 / 1000000000000), orderedInterval (-52801872159 / 1000000000000) (-52801872158 / 1000000000000)))) (orderedInterval (-8951569160 / 1000000000000) (-8951569067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (465125224507413 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-54435784351 / 1000000000000) (-54435784350 / 1000000000000), orderedInterval (-49881461029 / 1000000000000) (-49881461028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1262905464281239 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31881506715 / 1000000000000) (31881535631 / 1000000000000), orderedInterval (-31672238036 / 1000000000000) (-31672209120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1724389442366903 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38284648168 / 1000000000000) (-38284648063 / 1000000000000), orderedInterval (-3276317690 / 1000000000000) (-3276317584 / 1000000000000)))) (orderedInterval (1109690083 / 1000000000000) (1109690655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (729138809763861 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44671800353 / 1000000000000) (44671800354 / 1000000000000), orderedInterval (38566949411 / 1000000000000) (38566949412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2963908781113781 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9956019614 / 1000000000000) (9956019615 / 1000000000000), orderedInterval (27562109524 / 1000000000000) (27562109525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1979753706206779 / 4000000000000) 1 (IntervalRat.scale (797 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21649461656 / 1000000000000) (-21649458845 / 1000000000000), orderedInterval (28614903462 / 1000000000000) (28614906273 / 1000000000000)))) (orderedInterval (-10733657180 / 1000000000000) (-10733656369 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks1 :
    compactCertificate527.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate527.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate527_chunkChecks1_0
    compactCertificate527_chunkChecks1_1 compactCertificate527_chunkChecks1_2

theorem compactCertificate527_chunkChecks2_0 :
    compactCertificate527.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (797 / 2) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11919249524 / 1000000000000) (-11919249523 / 1000000000000), orderedInterval (-38135703214 / 1000000000000) (-38135703213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1174133185477097 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38970970740 / 1000000000000) (-38970900632 / 1000000000000), orderedInterval (25563032823 / 1000000000000) (25563102932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (379690548094601 / 800000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31166227827 / 1000000000000) (-31166227826 / 1000000000000), orderedInterval (-19202820665 / 1000000000000) (-19202820664 / 1000000000000)))) (orderedInterval (7556471950 / 1000000000000) (7556472342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (342609135192379 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86134262191 / 1000000000000) (-86134262135 / 1000000000000), orderedInterval (4159273076 / 1000000000000) (4159273131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (920296329088063 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52541520048 / 1000000000000) (-52541520006 / 1000000000000), orderedInterval (-2416226621 / 1000000000000) (-2416226578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2498783556605571 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9560390944 / 1000000000000) (-9560390943 / 1000000000000), orderedInterval (-30450297565 / 1000000000000) (-30450297564 / 1000000000000)))) (orderedInterval (-1082251597 / 1000000000000) (-1082251520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1840592658176923 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28687682837 / 1000000000000) (28687716985 / 1000000000000), orderedInterval (-23706621180 / 1000000000000) (-23706587032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3153886891683079 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18676635815 / 1000000000000) (-18676635814 / 1000000000000), orderedInterval (-21402942606 / 1000000000000) (-21402942605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2323138809763861 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12134066446 / 1000000000000) (-12134066445 / 1000000000000), orderedInterval (-30793807065 / 1000000000000) (-30793807064 / 1000000000000)))) (orderedInterval (-1632851165 / 1000000000000) (-1632851095 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks2_1 :
    compactCertificate527.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3564292356134203 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9264854975 / 1000000000000) (-9264854972 / 1000000000000), orderedInterval (25077180028 / 1000000000000) (25077180031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2057845151284387 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (888058172 / 1000000000000) (888058173 / 1000000000000), orderedInterval (35165331744 / 1000000000000) (35165331745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3651682332686783 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12605077603 / 1000000000000) (12605077628 / 1000000000000), orderedInterval (-23211561964 / 1000000000000) (-23211561938 / 1000000000000)))) (orderedInterval (-17709550386 / 1000000000000) (-17709549663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3411875318969627 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18803595307 / 1000000000000) (-18803594042 / 1000000000000), orderedInterval (19829761360 / 1000000000000) (19829762625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2434875219252491 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1132384954 / 1000000000000) (1132384955 / 1000000000000), orderedInterval (32318624572 / 1000000000000) (32318624573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2760888987264189 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4325723613 / 1000000000000) (-4325723612 / 1000000000000), orderedInterval (30063549665 / 1000000000000) (30063549667 / 1000000000000)))) (orderedInterval (-1879916138 / 1000000000000) (-1879915905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2301741400434541 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32128808669 / 1000000000000) (-32128808646 / 1000000000000), orderedInterval (-8578271537 / 1000000000000) (-8578271513 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2033658332097361 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9156032415 / 1000000000000) (9156032416 / 1000000000000), orderedInterval (34171899825 / 1000000000000) (34171899826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (589433450282739 / 800000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18874225185 / 1000000000000) (18874226407 / 1000000000000), orderedInterval (-22547373236 / 1000000000000) (-22547372014 / 1000000000000)))) (orderedInterval (-16207502 / 1000000000000) (-16207312 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks2_2 :
    compactCertificate527.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1630403943665033 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-828587404 / 1000000000000) (-828587402 / 1000000000000), orderedInterval (39512845878 / 1000000000000) (39512845879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1382111479274113 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28870481472 / 1000000000000) (28870481473 / 1000000000000), orderedInterval (31722213708 / 1000000000000) (31722213709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (864861190236139 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12382390838 / 1000000000000) (-12382390837 / 1000000000000), orderedInterval (-52801872159 / 1000000000000) (-52801872158 / 1000000000000)))) (orderedInterval (1231040688 / 1000000000000) (1231040777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (465125224507413 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-54435784351 / 1000000000000) (-54435784350 / 1000000000000), orderedInterval (-49881461029 / 1000000000000) (-49881461028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1262905464281239 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31881506715 / 1000000000000) (31881535631 / 1000000000000), orderedInterval (-31672238036 / 1000000000000) (-31672209120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1724389442366903 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38284648168 / 1000000000000) (-38284648063 / 1000000000000), orderedInterval (-3276317690 / 1000000000000) (-3276317584 / 1000000000000)))) (orderedInterval (-3068089943 / 1000000000000) (-3068089477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (729138809763861 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44671800353 / 1000000000000) (44671800354 / 1000000000000), orderedInterval (38566949411 / 1000000000000) (38566949412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2963908781113781 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9956019614 / 1000000000000) (9956019615 / 1000000000000), orderedInterval (27562109524 / 1000000000000) (27562109525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1979753706206779 / 4000000000000) 2 (IntervalRat.scale (797 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21649461656 / 1000000000000) (-21649458845 / 1000000000000), orderedInterval (28614903462 / 1000000000000) (28614906273 / 1000000000000)))) (orderedInterval (-3493334773 / 1000000000000) (-3493333728 / 1000000000000))) = true
  rfl'

theorem compactCertificate527_chunkChecks2 :
    compactCertificate527.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate527.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate527_chunkChecks2_0
    compactCertificate527_chunkChecks2_1 compactCertificate527_chunkChecks2_2

theorem compactCertificate527_chunkChecks3_0 :
    compactCertificate527.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (797 / 2) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11919249524 / 1000000000000) (-11919249523 / 1000000000000), orderedInterval (-38135703214 / 1000000000000) (-38135703213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1174133185477097 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38970970740 / 1000000000000) (-38970900632 / 1000000000000), orderedInterval (25563032823 / 1000000000000) (25563102932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (379690548094601 / 800000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31166227827 / 1000000000000) (-31166227826 / 1000000000000), orderedInterval (-19202820665 / 1000000000000) (-19202820664 / 1000000000000)))) (orderedInterval (16905092963 / 1000000000000) (16905093267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (342609135192379 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86134262191 / 1000000000000) (-86134262135 / 1000000000000), orderedInterval (4159273076 / 1000000000000) (4159273131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (920296329088063 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52541520048 / 1000000000000) (-52541520006 / 1000000000000), orderedInterval (-2416226621 / 1000000000000) (-2416226578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2498783556605571 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9560390944 / 1000000000000) (-9560390943 / 1000000000000), orderedInterval (-30450297565 / 1000000000000) (-30450297564 / 1000000000000)))) (orderedInterval (-8318930335 / 1000000000000) (-8318930222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1840592658176923 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28687682837 / 1000000000000) (28687716985 / 1000000000000), orderedInterval (-23706621180 / 1000000000000) (-23706587032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3153886891683079 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18676635815 / 1000000000000) (-18676635814 / 1000000000000), orderedInterval (-21402942606 / 1000000000000) (-21402942605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2323138809763861 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12134066446 / 1000000000000) (-12134066445 / 1000000000000), orderedInterval (-30793807065 / 1000000000000) (-30793807064 / 1000000000000)))) (orderedInterval (-2805485358 / 1000000000000) (-2805485231 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate527_chunkChecks3_1 :
    compactCertificate527.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3564292356134203 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9264854975 / 1000000000000) (-9264854972 / 1000000000000), orderedInterval (25077180028 / 1000000000000) (25077180031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2057845151284387 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (888058172 / 1000000000000) (888058173 / 1000000000000), orderedInterval (35165331744 / 1000000000000) (35165331745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3651682332686783 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12605077603 / 1000000000000) (12605077628 / 1000000000000), orderedInterval (-23211561964 / 1000000000000) (-23211561938 / 1000000000000)))) (orderedInterval (83928824302 / 1000000000000) (83928825890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3411875318969627 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18803595307 / 1000000000000) (-18803594042 / 1000000000000), orderedInterval (19829761360 / 1000000000000) (19829762625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2434875219252491 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1132384954 / 1000000000000) (1132384955 / 1000000000000), orderedInterval (32318624572 / 1000000000000) (32318624573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2760888987264189 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4325723613 / 1000000000000) (-4325723612 / 1000000000000), orderedInterval (30063549665 / 1000000000000) (30063549667 / 1000000000000)))) (orderedInterval (-6586884508 / 1000000000000) (-6586884067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2301741400434541 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32128808669 / 1000000000000) (-32128808646 / 1000000000000), orderedInterval (-8578271537 / 1000000000000) (-8578271513 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2033658332097361 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9156032415 / 1000000000000) (9156032416 / 1000000000000), orderedInterval (34171899825 / 1000000000000) (34171899826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (589433450282739 / 800000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18874225185 / 1000000000000) (18874226407 / 1000000000000), orderedInterval (-22547373236 / 1000000000000) (-22547372014 / 1000000000000)))) (orderedInterval (8008133118 / 1000000000000) (8008133444 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate527_chunkChecks3_2 :
    compactCertificate527.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1630403943665033 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-828587404 / 1000000000000) (-828587402 / 1000000000000), orderedInterval (39512845878 / 1000000000000) (39512845879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1382111479274113 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28870481472 / 1000000000000) (28870481473 / 1000000000000), orderedInterval (31722213708 / 1000000000000) (31722213709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (864861190236139 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12382390838 / 1000000000000) (-12382390837 / 1000000000000), orderedInterval (-52801872159 / 1000000000000) (-52801872158 / 1000000000000)))) (orderedInterval (8202471483 / 1000000000000) (8202471570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (465125224507413 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-54435784351 / 1000000000000) (-54435784350 / 1000000000000), orderedInterval (-49881461029 / 1000000000000) (-49881461028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1262905464281239 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31881506715 / 1000000000000) (31881535631 / 1000000000000), orderedInterval (-31672238036 / 1000000000000) (-31672209120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1724389442366903 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38284648168 / 1000000000000) (-38284648063 / 1000000000000), orderedInterval (-3276317690 / 1000000000000) (-3276317584 / 1000000000000)))) (orderedInterval (-690423409 / 1000000000000) (-690423027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (729138809763861 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44671800353 / 1000000000000) (44671800354 / 1000000000000), orderedInterval (38566949411 / 1000000000000) (38566949412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2963908781113781 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9956019614 / 1000000000000) (9956019615 / 1000000000000), orderedInterval (27562109524 / 1000000000000) (27562109525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1979753706206779 / 4000000000000) 3 (IntervalRat.scale (797 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21649461656 / 1000000000000) (-21649458845 / 1000000000000), orderedInterval (28614903462 / 1000000000000) (28614906273 / 1000000000000)))) (orderedInterval (24696322134 / 1000000000000) (24696323500 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate527_chunkChecks3 :
    compactCertificate527.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate527.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate527_chunkChecks3_0
    compactCertificate527_chunkChecks3_1 compactCertificate527_chunkChecks3_2

theorem compactCertificate527_chunkChecks4_0 :
    compactCertificate527.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (797 / 2) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11919249524 / 1000000000000) (-11919249523 / 1000000000000), orderedInterval (-38135703214 / 1000000000000) (-38135703213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1174133185477097 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38970970740 / 1000000000000) (-38970900632 / 1000000000000), orderedInterval (25563032823 / 1000000000000) (25563102932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (379690548094601 / 800000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31166227827 / 1000000000000) (-31166227826 / 1000000000000), orderedInterval (-19202820665 / 1000000000000) (-19202820664 / 1000000000000)))) (orderedInterval (-8595908153 / 1000000000000) (-8595907909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (342609135192379 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86134262191 / 1000000000000) (-86134262135 / 1000000000000), orderedInterval (4159273076 / 1000000000000) (4159273131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (920296329088063 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52541520048 / 1000000000000) (-52541520006 / 1000000000000), orderedInterval (-2416226621 / 1000000000000) (-2416226578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2498783556605571 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9560390944 / 1000000000000) (-9560390943 / 1000000000000), orderedInterval (-30450297565 / 1000000000000) (-30450297564 / 1000000000000)))) (orderedInterval (3934924429 / 1000000000000) (3934924604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1840592658176923 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28687682837 / 1000000000000) (28687716985 / 1000000000000), orderedInterval (-23706621180 / 1000000000000) (-23706587032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3153886891683079 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18676635815 / 1000000000000) (-18676635814 / 1000000000000), orderedInterval (-21402942606 / 1000000000000) (-21402942605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2323138809763861 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12134066446 / 1000000000000) (-12134066445 / 1000000000000), orderedInterval (-30793807065 / 1000000000000) (-30793807064 / 1000000000000)))) (orderedInterval (7519739905 / 1000000000000) (7519740138 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate527_chunkChecks4_1 :
    compactCertificate527.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3564292356134203 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9264854975 / 1000000000000) (-9264854972 / 1000000000000), orderedInterval (25077180028 / 1000000000000) (25077180031 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2057845151284387 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (888058172 / 1000000000000) (888058173 / 1000000000000), orderedInterval (35165331744 / 1000000000000) (35165331745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3651682332686783 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12605077603 / 1000000000000) (12605077628 / 1000000000000), orderedInterval (-23211561964 / 1000000000000) (-23211561938 / 1000000000000)))) (orderedInterval (90272520811 / 1000000000000) (90272524337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3411875318969627 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18803595307 / 1000000000000) (-18803594042 / 1000000000000), orderedInterval (19829761360 / 1000000000000) (19829762625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2434875219252491 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1132384954 / 1000000000000) (1132384955 / 1000000000000), orderedInterval (32318624572 / 1000000000000) (32318624573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2760888987264189 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4325723613 / 1000000000000) (-4325723612 / 1000000000000), orderedInterval (30063549665 / 1000000000000) (30063549667 / 1000000000000)))) (orderedInterval (7938501346 / 1000000000000) (7938502203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2301741400434541 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32128808669 / 1000000000000) (-32128808646 / 1000000000000), orderedInterval (-8578271537 / 1000000000000) (-8578271513 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2033658332097361 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9156032415 / 1000000000000) (9156032416 / 1000000000000), orderedInterval (34171899825 / 1000000000000) (34171899826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (589433450282739 / 800000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18874225185 / 1000000000000) (18874226407 / 1000000000000), orderedInterval (-22547373236 / 1000000000000) (-22547372014 / 1000000000000)))) (orderedInterval (2605780865 / 1000000000000) (2605781434 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate527_chunkChecks4_2 :
    compactCertificate527.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1630403943665033 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-828587404 / 1000000000000) (-828587402 / 1000000000000), orderedInterval (39512845878 / 1000000000000) (39512845879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1382111479274113 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28870481472 / 1000000000000) (28870481473 / 1000000000000), orderedInterval (31722213708 / 1000000000000) (31722213709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (864861190236139 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12382390838 / 1000000000000) (-12382390837 / 1000000000000), orderedInterval (-52801872159 / 1000000000000) (-52801872158 / 1000000000000)))) (orderedInterval (-854696152 / 1000000000000) (-854696067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (465125224507413 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-54435784351 / 1000000000000) (-54435784350 / 1000000000000), orderedInterval (-49881461029 / 1000000000000) (-49881461028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1262905464281239 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31881506715 / 1000000000000) (31881535631 / 1000000000000), orderedInterval (-31672238036 / 1000000000000) (-31672209120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1724389442366903 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38284648168 / 1000000000000) (-38284648063 / 1000000000000), orderedInterval (-3276317690 / 1000000000000) (-3276317584 / 1000000000000)))) (orderedInterval (3744214568 / 1000000000000) (3744214885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (729138809763861 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (44671800353 / 1000000000000) (44671800354 / 1000000000000), orderedInterval (38566949411 / 1000000000000) (38566949412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2963908781113781 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9956019614 / 1000000000000) (9956019615 / 1000000000000), orderedInterval (27562109524 / 1000000000000) (27562109525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1979753706206779 / 4000000000000) 4 (IntervalRat.scale (797 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21649461656 / 1000000000000) (-21649458845 / 1000000000000), orderedInterval (28614903462 / 1000000000000) (28614906273 / 1000000000000)))) (orderedInterval (-134304405 / 1000000000000) (-134302577 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate527_chunkChecks4 :
    compactCertificate527.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate527.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate527_chunkChecks4_0
    compactCertificate527_chunkChecks4_1 compactCertificate527_chunkChecks4_2

theorem compactCertificate527_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate527.chunkCheck r b = true :=
  compactCertificate527.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate527_chunkChecks0
    · exact compactCertificate527_chunkChecks1
    · exact compactCertificate527_chunkChecks2
    · exact compactCertificate527_chunkChecks3
    · exact compactCertificate527_chunkChecks4)

theorem compactCertificate527_coefficient0 :
    compactCertificate527.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate527_coefficient1 :
    compactCertificate527.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate527_coefficient2 :
    compactCertificate527.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate527_coefficient3 :
    compactCertificate527.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate527_coefficient4 :
    compactCertificate527.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate527_coefficients : ∀ r : Fin 5,
    compactCertificate527.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate527_coefficient0
  · exact compactCertificate527_coefficient1
  · exact compactCertificate527_coefficient2
  · exact compactCertificate527_coefficient3
  · exact compactCertificate527_coefficient4

theorem compactCertificate527_lower : (1 : ℚ) ≤ compactCertificate527.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate527, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate527_proves {t : ℝ} (ht : t ∈ compactCertificate527.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate527.proves compactCertificate527_states compactCertificate527_chunks
    compactCertificate527_coefficients compactCertificate527_lower ht

end Erdos232
