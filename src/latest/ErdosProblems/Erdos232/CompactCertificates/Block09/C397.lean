/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate397 : CompactCertificate where
  left := 268
  right := 269
  center := 537 / 2
  grid := fun i =>
    match i.val with
    | 0 => 86
    | 1 => 63
    | 2 => 102
    | 3 => 18
    | 4 => 49
    | 5 => 134
    | 6 => 99
    | 7 => 169
    | 8 => 125
    | 9 => 191
    | 10 => 110
    | 11 => 196
    | 12 => 183
    | 13 => 131
    | 14 => 148
    | 15 => 123
    | 16 => 109
    | 17 => 158
    | 18 => 87
    | 19 => 74
    | 20 => 46
    | 21 => 25
    | 22 => 68
    | 23 => 93
    | 24 => 39
    | 25 => 159
    | _ => 106
  point := fun i =>
    match i.val with
    | 0 => 537 / 2
    | 1 => 791103539022837 / 4000000000000
    | 2 => 255826630272021 / 800000000000
    | 3 => 230842039646559 / 4000000000000
    | 4 => 620074189109523 / 4000000000000
    | 5 => 1683622045040391 / 4000000000000
    | 6 => 1240148378219583 / 4000000000000
    | 7 => 2125015383731259 / 4000000000000
    | 8 => 1565276713730481 / 4000000000000
    | 9 => 2401537007834463 / 4000000000000
    | 10 => 1386528037941927 / 4000000000000
    | 11 => 2460418334570643 / 4000000000000
    | 12 => 2298841965227967 / 4000000000000
    | 13 => 1640562098793711 / 4000000000000
    | 14 => 1860222567328569 / 4000000000000
    | 15 => 1550859638686761 / 4000000000000
    | 16 => 1370231523633981 / 4000000000000
    | 17 => 397146502888119 / 800000000000
    | 18 => 1098528127663893 / 4000000000000
    | 19 => 931234459686573 / 4000000000000
    | 20 => 582723286269519 / 4000000000000
    | 21 => 313390521405873 / 4000000000000
    | 22 => 850916228756619 / 4000000000000
    | 23 => 1161853363301163 / 4000000000000
    | 24 => 491276713730481 / 4000000000000
    | 25 => 1997012566446801 / 4000000000000
    | _ => 1333911844708959 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-37900393016 / 1000000000000) (-37900305008 / 1000000000000), orderedInterval (30641530229 / 1000000000000) (30641618238 / 1000000000000))
    | 1 => (orderedInterval (-33896286283 / 1000000000000) (-33896286282 / 1000000000000), orderedInterval (-45410895163 / 1000000000000) (-45410895162 / 1000000000000))
    | 2 => (orderedInterval (5600142348 / 1000000000000) (5600142349 / 1000000000000), orderedInterval (44256645272 / 1000000000000) (44256645273 / 1000000000000))
    | 3 => (orderedInterval (97756945802 / 1000000000000) (97756948902 / 1000000000000), orderedInterval (-39246615516 / 1000000000000) (-39246612416 / 1000000000000))
    | 4 => (orderedInterval (-61328331024 / 1000000000000) (-61328328847 / 1000000000000), orderedInterval (18786811341 / 1000000000000) (18786813518 / 1000000000000))
    | 5 => (orderedInterval (25561980456 / 1000000000000) (25561980457 / 1000000000000), orderedInterval (29279799090 / 1000000000000) (29279799091 / 1000000000000))
    | 6 => (orderedInterval (8806271003 / 1000000000000) (8806271029 / 1000000000000), orderedInterval (-44464382172 / 1000000000000) (-44464382145 / 1000000000000))
    | 7 => (orderedInterval (-31004061334 / 1000000000000) (-31004061332 / 1000000000000), orderedInterval (-15368296550 / 1000000000000) (-15368296549 / 1000000000000))
    | 8 => (orderedInterval (22601854665 / 1000000000000) (22601857453 / 1000000000000), orderedInterval (-33435648132 / 1000000000000) (-33435645344 / 1000000000000))
    | 9 => (orderedInterval (-29384042881 / 1000000000000) (-29384042879 / 1000000000000), orderedInterval (-14008763649 / 1000000000000) (-14008763647 / 1000000000000))
    | 10 => (orderedInterval (41290653683 / 1000000000000) (41290658523 / 1000000000000), orderedInterval (-11534180672 / 1000000000000) (-11534175833 / 1000000000000))
    | 11 => (orderedInterval (4413372407 / 1000000000000) (4413372408 / 1000000000000), orderedInterval (31863332211 / 1000000000000) (31863332212 / 1000000000000))
    | 12 => (orderedInterval (-18356803777 / 1000000000000) (-18356803776 / 1000000000000), orderedInterval (-27746422654 / 1000000000000) (-27746422653 / 1000000000000))
    | 13 => (orderedInterval (22988306137 / 1000000000000) (22988309555 / 1000000000000), orderedInterval (-32023920259 / 1000000000000) (-32023916842 / 1000000000000))
    | 14 => (orderedInterval (28635285378 / 1000000000000) (28635285379 / 1000000000000), orderedInterval (23398494987 / 1000000000000) (23398494988 / 1000000000000))
    | 15 => (orderedInterval (-35299465424 / 1000000000000) (-35299405617 / 1000000000000), orderedInterval (19943435378 / 1000000000000) (19943495185 / 1000000000000))
    | 16 => (orderedInterval (-34016966970 / 1000000000000) (-34016966969 / 1000000000000), orderedInterval (-26431951126 / 1000000000000) (-26431951125 / 1000000000000))
    | 17 => (orderedInterval (26824012019 / 1000000000000) (26824012020 / 1000000000000), orderedInterval (23697655441 / 1000000000000) (23697655442 / 1000000000000))
    | 18 => (orderedInterval (-41598966978 / 1000000000000) (-41598926010 / 1000000000000), orderedInterval (24316350404 / 1000000000000) (24316391372 / 1000000000000))
    | 19 => (orderedInterval (46968325821 / 1000000000000) (46968325822 / 1000000000000), orderedInterval (22888088111 / 1000000000000) (22888088112 / 1000000000000))
    | 20 => (orderedInterval (61357827520 / 1000000000000) (61357832829 / 1000000000000), orderedInterval (-24810607532 / 1000000000000) (-24810602222 / 1000000000000))
    | 21 => (orderedInterval (-50272017811 / 1000000000000) (-50272017810 / 1000000000000), orderedInterval (-74501406551 / 1000000000000) (-74501406550 / 1000000000000))
    | 22 => (orderedInterval (-6246372779 / 1000000000000) (-6246372762 / 1000000000000), orderedInterval (54361924450 / 1000000000000) (54361924466 / 1000000000000))
    | 23 => (orderedInterval (37241370960 / 1000000000000) (37241472181 / 1000000000000), orderedInterval (-28433405346 / 1000000000000) (-28433304125 / 1000000000000))
    | 24 => (orderedInterval (-63545947030 / 1000000000000) (-63545947029 / 1000000000000), orderedInterval (-33583281435 / 1000000000000) (-33583281434 / 1000000000000))
    | 25 => (orderedInterval (-17899668010 / 1000000000000) (-17899668009 / 1000000000000), orderedInterval (-30881045278 / 1000000000000) (-30881045277 / 1000000000000))
    | _ => (orderedInterval (41520446862 / 1000000000000) (41520446864 / 1000000000000), orderedInterval (13542223043 / 1000000000000) (13542223045 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15009613914 / 1000000000000) (-15009579012 / 1000000000000)
      | 1 => orderedInterval (-5116990061 / 1000000000000) (-5116989915 / 1000000000000)
      | 2 => orderedInterval (1502531525 / 1000000000000) (1502531608 / 1000000000000)
      | 3 => orderedInterval (8907874132 / 1000000000000) (8907874598 / 1000000000000)
      | 4 => orderedInterval (2360326016 / 1000000000000) (2360326372 / 1000000000000)
      | 5 => orderedInterval (2225852053 / 1000000000000) (2225852770 / 1000000000000)
      | 6 => orderedInterval (5990469358 / 1000000000000) (5990476150 / 1000000000000)
      | 7 => orderedInterval (-1784155074 / 1000000000000) (-1784147283 / 1000000000000)
      | _ => orderedInterval (-6716348310 / 1000000000000) (-6716348235 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14926606981 / 1000000000000) (14926641886 / 1000000000000)
      | 1 => orderedInterval (-2775435613 / 1000000000000) (-2775435523 / 1000000000000)
      | 2 => orderedInterval (-239813414 / 1000000000000) (-239813289 / 1000000000000)
      | 3 => orderedInterval (14839460710 / 1000000000000) (14839461395 / 1000000000000)
      | 4 => orderedInterval (-3758687286 / 1000000000000) (-3758686740 / 1000000000000)
      | 5 => orderedInterval (3384211590 / 1000000000000) (3384212625 / 1000000000000)
      | 6 => orderedInterval (-5538306980 / 1000000000000) (-5538300124 / 1000000000000)
      | 7 => orderedInterval (1781637147 / 1000000000000) (1781645569 / 1000000000000)
      | _ => orderedInterval (1425758251 / 1000000000000) (1425758356 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14671987281 / 1000000000000) (14672022319 / 1000000000000)
      | 1 => orderedInterval (5271352245 / 1000000000000) (5271352325 / 1000000000000)
      | 2 => orderedInterval (-4903109928 / 1000000000000) (-4903109737 / 1000000000000)
      | 3 => orderedInterval (-34552690532 / 1000000000000) (-34552689457 / 1000000000000)
      | 4 => orderedInterval (-6141864527 / 1000000000000) (-6141863684 / 1000000000000)
      | 5 => orderedInterval (-4679102602 / 1000000000000) (-4679101102 / 1000000000000)
      | 6 => orderedInterval (-5527430569 / 1000000000000) (-5527423579 / 1000000000000)
      | 7 => orderedInterval (3165543013 / 1000000000000) (3165552153 / 1000000000000)
      | _ => orderedInterval (7054312223 / 1000000000000) (7054312379 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16418033490 / 1000000000000) (-16417998448 / 1000000000000)
      | 1 => orderedInterval (7862633255 / 1000000000000) (7862633347 / 1000000000000)
      | 2 => orderedInterval (-1151901640 / 1000000000000) (-1151901345 / 1000000000000)
      | 3 => orderedInterval (-80321348814 / 1000000000000) (-80321346999 / 1000000000000)
      | 4 => orderedInterval (6519382363 / 1000000000000) (6519383664 / 1000000000000)
      | 5 => orderedInterval (-7652129106 / 1000000000000) (-7652126935 / 1000000000000)
      | 6 => orderedInterval (5154517675 / 1000000000000) (5154524796 / 1000000000000)
      | 7 => orderedInterval (-2191375070 / 1000000000000) (-2191365185 / 1000000000000)
      | _ => orderedInterval (-11299375606 / 1000000000000) (-11299375366 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14331656754 / 1000000000000) (-14331621579 / 1000000000000)
      | 1 => orderedInterval (-11283486008 / 1000000000000) (-11283485881 / 1000000000000)
      | 2 => orderedInterval (17129203569 / 1000000000000) (17129204033 / 1000000000000)
      | 3 => orderedInterval (156906019194 / 1000000000000) (156906022510 / 1000000000000)
      | 4 => orderedInterval (17438638425 / 1000000000000) (17438640447 / 1000000000000)
      | 5 => orderedInterval (11468255052 / 1000000000000) (11468258206 / 1000000000000)
      | 6 => orderedInterval (5912155409 / 1000000000000) (5912162703 / 1000000000000)
      | 7 => orderedInterval (-3830050747 / 1000000000000) (-3830040018 / 1000000000000)
      | _ => orderedInterval (-1052393005 / 1000000000000) (-1052392621 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-7640054275 / 1000000000000) (-7640002947 / 1000000000000)
    | 1 => orderedInterval (24045431386 / 1000000000000) (24045484155 / 1000000000000)
    | 2 => orderedInterval (-25641003396 / 1000000000000) (-25640948383 / 1000000000000)
    | 3 => orderedInterval (-99497630433 / 1000000000000) (-99497572471 / 1000000000000)
    | _ => orderedInterval (178356685135 / 1000000000000) (178356747800 / 1000000000000)

theorem compactCertificate397_stateChecks0 :
    compactCertificate397.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (537 / 2)) (orderedInterval (-37900393016 / 1000000000000) (-37900305008 / 1000000000000), orderedInterval (30641530229 / 1000000000000) (30641618238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (791103539022837 / 4000000000000)) (orderedInterval (-33896286283 / 1000000000000) (-33896286282 / 1000000000000), orderedInterval (-45410895163 / 1000000000000) (-45410895162 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (255826630272021 / 800000000000)) (orderedInterval (5600142348 / 1000000000000) (5600142349 / 1000000000000), orderedInterval (44256645272 / 1000000000000) (44256645273 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_stateChecks1 :
    compactCertificate397.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (230842039646559 / 4000000000000)) (orderedInterval (97756945802 / 1000000000000) (97756948902 / 1000000000000), orderedInterval (-39246615516 / 1000000000000) (-39246612416 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (620074189109523 / 4000000000000)) (orderedInterval (-61328331024 / 1000000000000) (-61328328847 / 1000000000000), orderedInterval (18786811341 / 1000000000000) (18786813518 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1683622045040391 / 4000000000000)) (orderedInterval (25561980456 / 1000000000000) (25561980457 / 1000000000000), orderedInterval (29279799090 / 1000000000000) (29279799091 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_stateChecks2 :
    compactCertificate397.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1240148378219583 / 4000000000000)) (orderedInterval (8806271003 / 1000000000000) (8806271029 / 1000000000000), orderedInterval (-44464382172 / 1000000000000) (-44464382145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2125015383731259 / 4000000000000)) (orderedInterval (-31004061334 / 1000000000000) (-31004061332 / 1000000000000), orderedInterval (-15368296550 / 1000000000000) (-15368296549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1565276713730481 / 4000000000000)) (orderedInterval (22601854665 / 1000000000000) (22601857453 / 1000000000000), orderedInterval (-33435648132 / 1000000000000) (-33435645344 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_stateChecks3 :
    compactCertificate397.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2401537007834463 / 4000000000000)) (orderedInterval (-29384042881 / 1000000000000) (-29384042879 / 1000000000000), orderedInterval (-14008763649 / 1000000000000) (-14008763647 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1386528037941927 / 4000000000000)) (orderedInterval (41290653683 / 1000000000000) (41290658523 / 1000000000000), orderedInterval (-11534180672 / 1000000000000) (-11534175833 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2460418334570643 / 4000000000000)) (orderedInterval (4413372407 / 1000000000000) (4413372408 / 1000000000000), orderedInterval (31863332211 / 1000000000000) (31863332212 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_stateChecks4 :
    compactCertificate397.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2298841965227967 / 4000000000000)) (orderedInterval (-18356803777 / 1000000000000) (-18356803776 / 1000000000000), orderedInterval (-27746422654 / 1000000000000) (-27746422653 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1640562098793711 / 4000000000000)) (orderedInterval (22988306137 / 1000000000000) (22988309555 / 1000000000000), orderedInterval (-32023920259 / 1000000000000) (-32023916842 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1860222567328569 / 4000000000000)) (orderedInterval (28635285378 / 1000000000000) (28635285379 / 1000000000000), orderedInterval (23398494987 / 1000000000000) (23398494988 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_stateChecks5 :
    compactCertificate397.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1550859638686761 / 4000000000000)) (orderedInterval (-35299465424 / 1000000000000) (-35299405617 / 1000000000000), orderedInterval (19943435378 / 1000000000000) (19943495185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1370231523633981 / 4000000000000)) (orderedInterval (-34016966970 / 1000000000000) (-34016966969 / 1000000000000), orderedInterval (-26431951126 / 1000000000000) (-26431951125 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (397146502888119 / 800000000000)) (orderedInterval (26824012019 / 1000000000000) (26824012020 / 1000000000000), orderedInterval (23697655441 / 1000000000000) (23697655442 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_stateChecks6 :
    compactCertificate397.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1098528127663893 / 4000000000000)) (orderedInterval (-41598966978 / 1000000000000) (-41598926010 / 1000000000000), orderedInterval (24316350404 / 1000000000000) (24316391372 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (931234459686573 / 4000000000000)) (orderedInterval (46968325821 / 1000000000000) (46968325822 / 1000000000000), orderedInterval (22888088111 / 1000000000000) (22888088112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (582723286269519 / 4000000000000)) (orderedInterval (61357827520 / 1000000000000) (61357832829 / 1000000000000), orderedInterval (-24810607532 / 1000000000000) (-24810602222 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_stateChecks7 :
    compactCertificate397.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (313390521405873 / 4000000000000)) (orderedInterval (-50272017811 / 1000000000000) (-50272017810 / 1000000000000), orderedInterval (-74501406551 / 1000000000000) (-74501406550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (850916228756619 / 4000000000000)) (orderedInterval (-6246372779 / 1000000000000) (-6246372762 / 1000000000000), orderedInterval (54361924450 / 1000000000000) (54361924466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1161853363301163 / 4000000000000)) (orderedInterval (37241370960 / 1000000000000) (37241472181 / 1000000000000), orderedInterval (-28433405346 / 1000000000000) (-28433304125 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_stateChecks8 :
    compactCertificate397.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (491276713730481 / 4000000000000)) (orderedInterval (-63545947030 / 1000000000000) (-63545947029 / 1000000000000), orderedInterval (-33583281435 / 1000000000000) (-33583281434 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1997012566446801 / 4000000000000)) (orderedInterval (-17899668010 / 1000000000000) (-17899668009 / 1000000000000), orderedInterval (-30881045278 / 1000000000000) (-30881045277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1333911844708959 / 4000000000000)) (orderedInterval (41520446862 / 1000000000000) (41520446864 / 1000000000000), orderedInterval (13542223043 / 1000000000000) (13542223045 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_states : ∀ j,
    BesselStateValid (compactCertificate397.point j) (compactCertificate397.state j) :=
  compactCertificate397.statesValid_of_checks3 compactCertificate397_stateChecks0
    compactCertificate397_stateChecks1 compactCertificate397_stateChecks2
    compactCertificate397_stateChecks3 compactCertificate397_stateChecks4
    compactCertificate397_stateChecks5 compactCertificate397_stateChecks6
    compactCertificate397_stateChecks7 compactCertificate397_stateChecks8

theorem compactCertificate397_chunkChecks0_0 :
    compactCertificate397.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (537 / 2) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37900393016 / 1000000000000) (-37900305008 / 1000000000000), orderedInterval (30641530229 / 1000000000000) (30641618238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (791103539022837 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33896286283 / 1000000000000) (-33896286282 / 1000000000000), orderedInterval (-45410895163 / 1000000000000) (-45410895162 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (255826630272021 / 800000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5600142348 / 1000000000000) (5600142349 / 1000000000000), orderedInterval (44256645272 / 1000000000000) (44256645273 / 1000000000000)))) (orderedInterval (-15009613914 / 1000000000000) (-15009579012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (230842039646559 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97756945802 / 1000000000000) (97756948902 / 1000000000000), orderedInterval (-39246615516 / 1000000000000) (-39246612416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (620074189109523 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61328331024 / 1000000000000) (-61328328847 / 1000000000000), orderedInterval (18786811341 / 1000000000000) (18786813518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1683622045040391 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25561980456 / 1000000000000) (25561980457 / 1000000000000), orderedInterval (29279799090 / 1000000000000) (29279799091 / 1000000000000)))) (orderedInterval (-5116990061 / 1000000000000) (-5116989915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1240148378219583 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8806271003 / 1000000000000) (8806271029 / 1000000000000), orderedInterval (-44464382172 / 1000000000000) (-44464382145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2125015383731259 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31004061334 / 1000000000000) (-31004061332 / 1000000000000), orderedInterval (-15368296550 / 1000000000000) (-15368296549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1565276713730481 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22601854665 / 1000000000000) (22601857453 / 1000000000000), orderedInterval (-33435648132 / 1000000000000) (-33435645344 / 1000000000000)))) (orderedInterval (1502531525 / 1000000000000) (1502531608 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks0_1 :
    compactCertificate397.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2401537007834463 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29384042881 / 1000000000000) (-29384042879 / 1000000000000), orderedInterval (-14008763649 / 1000000000000) (-14008763647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1386528037941927 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41290653683 / 1000000000000) (41290658523 / 1000000000000), orderedInterval (-11534180672 / 1000000000000) (-11534175833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2460418334570643 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4413372407 / 1000000000000) (4413372408 / 1000000000000), orderedInterval (31863332211 / 1000000000000) (31863332212 / 1000000000000)))) (orderedInterval (8907874132 / 1000000000000) (8907874598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2298841965227967 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18356803777 / 1000000000000) (-18356803776 / 1000000000000), orderedInterval (-27746422654 / 1000000000000) (-27746422653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1640562098793711 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22988306137 / 1000000000000) (22988309555 / 1000000000000), orderedInterval (-32023920259 / 1000000000000) (-32023916842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1860222567328569 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28635285378 / 1000000000000) (28635285379 / 1000000000000), orderedInterval (23398494987 / 1000000000000) (23398494988 / 1000000000000)))) (orderedInterval (2360326016 / 1000000000000) (2360326372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1550859638686761 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35299465424 / 1000000000000) (-35299405617 / 1000000000000), orderedInterval (19943435378 / 1000000000000) (19943495185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1370231523633981 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34016966970 / 1000000000000) (-34016966969 / 1000000000000), orderedInterval (-26431951126 / 1000000000000) (-26431951125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (397146502888119 / 800000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26824012019 / 1000000000000) (26824012020 / 1000000000000), orderedInterval (23697655441 / 1000000000000) (23697655442 / 1000000000000)))) (orderedInterval (2225852053 / 1000000000000) (2225852770 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks0_2 :
    compactCertificate397.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1098528127663893 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41598966978 / 1000000000000) (-41598926010 / 1000000000000), orderedInterval (24316350404 / 1000000000000) (24316391372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (931234459686573 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46968325821 / 1000000000000) (46968325822 / 1000000000000), orderedInterval (22888088111 / 1000000000000) (22888088112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (582723286269519 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61357827520 / 1000000000000) (61357832829 / 1000000000000), orderedInterval (-24810607532 / 1000000000000) (-24810602222 / 1000000000000)))) (orderedInterval (5990469358 / 1000000000000) (5990476150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (313390521405873 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50272017811 / 1000000000000) (-50272017810 / 1000000000000), orderedInterval (-74501406551 / 1000000000000) (-74501406550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (850916228756619 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6246372779 / 1000000000000) (-6246372762 / 1000000000000), orderedInterval (54361924450 / 1000000000000) (54361924466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1161853363301163 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37241370960 / 1000000000000) (37241472181 / 1000000000000), orderedInterval (-28433405346 / 1000000000000) (-28433304125 / 1000000000000)))) (orderedInterval (-1784155074 / 1000000000000) (-1784147283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (491276713730481 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63545947030 / 1000000000000) (-63545947029 / 1000000000000), orderedInterval (-33583281435 / 1000000000000) (-33583281434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1997012566446801 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17899668010 / 1000000000000) (-17899668009 / 1000000000000), orderedInterval (-30881045278 / 1000000000000) (-30881045277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1333911844708959 / 4000000000000) 0 (IntervalRat.scale (537 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41520446862 / 1000000000000) (41520446864 / 1000000000000), orderedInterval (13542223043 / 1000000000000) (13542223045 / 1000000000000)))) (orderedInterval (-6716348310 / 1000000000000) (-6716348235 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks0 :
    compactCertificate397.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate397.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate397_chunkChecks0_0
    compactCertificate397_chunkChecks0_1 compactCertificate397_chunkChecks0_2

theorem compactCertificate397_chunkChecks1_0 :
    compactCertificate397.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (537 / 2) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37900393016 / 1000000000000) (-37900305008 / 1000000000000), orderedInterval (30641530229 / 1000000000000) (30641618238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (791103539022837 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33896286283 / 1000000000000) (-33896286282 / 1000000000000), orderedInterval (-45410895163 / 1000000000000) (-45410895162 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (255826630272021 / 800000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5600142348 / 1000000000000) (5600142349 / 1000000000000), orderedInterval (44256645272 / 1000000000000) (44256645273 / 1000000000000)))) (orderedInterval (14926606981 / 1000000000000) (14926641886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (230842039646559 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97756945802 / 1000000000000) (97756948902 / 1000000000000), orderedInterval (-39246615516 / 1000000000000) (-39246612416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (620074189109523 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61328331024 / 1000000000000) (-61328328847 / 1000000000000), orderedInterval (18786811341 / 1000000000000) (18786813518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1683622045040391 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25561980456 / 1000000000000) (25561980457 / 1000000000000), orderedInterval (29279799090 / 1000000000000) (29279799091 / 1000000000000)))) (orderedInterval (-2775435613 / 1000000000000) (-2775435523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1240148378219583 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8806271003 / 1000000000000) (8806271029 / 1000000000000), orderedInterval (-44464382172 / 1000000000000) (-44464382145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2125015383731259 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31004061334 / 1000000000000) (-31004061332 / 1000000000000), orderedInterval (-15368296550 / 1000000000000) (-15368296549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1565276713730481 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22601854665 / 1000000000000) (22601857453 / 1000000000000), orderedInterval (-33435648132 / 1000000000000) (-33435645344 / 1000000000000)))) (orderedInterval (-239813414 / 1000000000000) (-239813289 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks1_1 :
    compactCertificate397.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2401537007834463 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29384042881 / 1000000000000) (-29384042879 / 1000000000000), orderedInterval (-14008763649 / 1000000000000) (-14008763647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1386528037941927 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41290653683 / 1000000000000) (41290658523 / 1000000000000), orderedInterval (-11534180672 / 1000000000000) (-11534175833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2460418334570643 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4413372407 / 1000000000000) (4413372408 / 1000000000000), orderedInterval (31863332211 / 1000000000000) (31863332212 / 1000000000000)))) (orderedInterval (14839460710 / 1000000000000) (14839461395 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2298841965227967 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18356803777 / 1000000000000) (-18356803776 / 1000000000000), orderedInterval (-27746422654 / 1000000000000) (-27746422653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1640562098793711 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22988306137 / 1000000000000) (22988309555 / 1000000000000), orderedInterval (-32023920259 / 1000000000000) (-32023916842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1860222567328569 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28635285378 / 1000000000000) (28635285379 / 1000000000000), orderedInterval (23398494987 / 1000000000000) (23398494988 / 1000000000000)))) (orderedInterval (-3758687286 / 1000000000000) (-3758686740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1550859638686761 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35299465424 / 1000000000000) (-35299405617 / 1000000000000), orderedInterval (19943435378 / 1000000000000) (19943495185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1370231523633981 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34016966970 / 1000000000000) (-34016966969 / 1000000000000), orderedInterval (-26431951126 / 1000000000000) (-26431951125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (397146502888119 / 800000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26824012019 / 1000000000000) (26824012020 / 1000000000000), orderedInterval (23697655441 / 1000000000000) (23697655442 / 1000000000000)))) (orderedInterval (3384211590 / 1000000000000) (3384212625 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks1_2 :
    compactCertificate397.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1098528127663893 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41598966978 / 1000000000000) (-41598926010 / 1000000000000), orderedInterval (24316350404 / 1000000000000) (24316391372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (931234459686573 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46968325821 / 1000000000000) (46968325822 / 1000000000000), orderedInterval (22888088111 / 1000000000000) (22888088112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (582723286269519 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61357827520 / 1000000000000) (61357832829 / 1000000000000), orderedInterval (-24810607532 / 1000000000000) (-24810602222 / 1000000000000)))) (orderedInterval (-5538306980 / 1000000000000) (-5538300124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (313390521405873 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50272017811 / 1000000000000) (-50272017810 / 1000000000000), orderedInterval (-74501406551 / 1000000000000) (-74501406550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (850916228756619 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6246372779 / 1000000000000) (-6246372762 / 1000000000000), orderedInterval (54361924450 / 1000000000000) (54361924466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1161853363301163 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37241370960 / 1000000000000) (37241472181 / 1000000000000), orderedInterval (-28433405346 / 1000000000000) (-28433304125 / 1000000000000)))) (orderedInterval (1781637147 / 1000000000000) (1781645569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (491276713730481 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63545947030 / 1000000000000) (-63545947029 / 1000000000000), orderedInterval (-33583281435 / 1000000000000) (-33583281434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1997012566446801 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17899668010 / 1000000000000) (-17899668009 / 1000000000000), orderedInterval (-30881045278 / 1000000000000) (-30881045277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1333911844708959 / 4000000000000) 1 (IntervalRat.scale (537 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41520446862 / 1000000000000) (41520446864 / 1000000000000), orderedInterval (13542223043 / 1000000000000) (13542223045 / 1000000000000)))) (orderedInterval (1425758251 / 1000000000000) (1425758356 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks1 :
    compactCertificate397.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate397.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate397_chunkChecks1_0
    compactCertificate397_chunkChecks1_1 compactCertificate397_chunkChecks1_2

theorem compactCertificate397_chunkChecks2_0 :
    compactCertificate397.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (537 / 2) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37900393016 / 1000000000000) (-37900305008 / 1000000000000), orderedInterval (30641530229 / 1000000000000) (30641618238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (791103539022837 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33896286283 / 1000000000000) (-33896286282 / 1000000000000), orderedInterval (-45410895163 / 1000000000000) (-45410895162 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (255826630272021 / 800000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5600142348 / 1000000000000) (5600142349 / 1000000000000), orderedInterval (44256645272 / 1000000000000) (44256645273 / 1000000000000)))) (orderedInterval (14671987281 / 1000000000000) (14672022319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (230842039646559 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97756945802 / 1000000000000) (97756948902 / 1000000000000), orderedInterval (-39246615516 / 1000000000000) (-39246612416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (620074189109523 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61328331024 / 1000000000000) (-61328328847 / 1000000000000), orderedInterval (18786811341 / 1000000000000) (18786813518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1683622045040391 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25561980456 / 1000000000000) (25561980457 / 1000000000000), orderedInterval (29279799090 / 1000000000000) (29279799091 / 1000000000000)))) (orderedInterval (5271352245 / 1000000000000) (5271352325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1240148378219583 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8806271003 / 1000000000000) (8806271029 / 1000000000000), orderedInterval (-44464382172 / 1000000000000) (-44464382145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2125015383731259 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31004061334 / 1000000000000) (-31004061332 / 1000000000000), orderedInterval (-15368296550 / 1000000000000) (-15368296549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1565276713730481 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22601854665 / 1000000000000) (22601857453 / 1000000000000), orderedInterval (-33435648132 / 1000000000000) (-33435645344 / 1000000000000)))) (orderedInterval (-4903109928 / 1000000000000) (-4903109737 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks2_1 :
    compactCertificate397.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2401537007834463 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29384042881 / 1000000000000) (-29384042879 / 1000000000000), orderedInterval (-14008763649 / 1000000000000) (-14008763647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1386528037941927 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41290653683 / 1000000000000) (41290658523 / 1000000000000), orderedInterval (-11534180672 / 1000000000000) (-11534175833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2460418334570643 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4413372407 / 1000000000000) (4413372408 / 1000000000000), orderedInterval (31863332211 / 1000000000000) (31863332212 / 1000000000000)))) (orderedInterval (-34552690532 / 1000000000000) (-34552689457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2298841965227967 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18356803777 / 1000000000000) (-18356803776 / 1000000000000), orderedInterval (-27746422654 / 1000000000000) (-27746422653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1640562098793711 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22988306137 / 1000000000000) (22988309555 / 1000000000000), orderedInterval (-32023920259 / 1000000000000) (-32023916842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1860222567328569 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28635285378 / 1000000000000) (28635285379 / 1000000000000), orderedInterval (23398494987 / 1000000000000) (23398494988 / 1000000000000)))) (orderedInterval (-6141864527 / 1000000000000) (-6141863684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1550859638686761 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35299465424 / 1000000000000) (-35299405617 / 1000000000000), orderedInterval (19943435378 / 1000000000000) (19943495185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1370231523633981 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34016966970 / 1000000000000) (-34016966969 / 1000000000000), orderedInterval (-26431951126 / 1000000000000) (-26431951125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (397146502888119 / 800000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26824012019 / 1000000000000) (26824012020 / 1000000000000), orderedInterval (23697655441 / 1000000000000) (23697655442 / 1000000000000)))) (orderedInterval (-4679102602 / 1000000000000) (-4679101102 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks2_2 :
    compactCertificate397.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1098528127663893 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41598966978 / 1000000000000) (-41598926010 / 1000000000000), orderedInterval (24316350404 / 1000000000000) (24316391372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (931234459686573 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46968325821 / 1000000000000) (46968325822 / 1000000000000), orderedInterval (22888088111 / 1000000000000) (22888088112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (582723286269519 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61357827520 / 1000000000000) (61357832829 / 1000000000000), orderedInterval (-24810607532 / 1000000000000) (-24810602222 / 1000000000000)))) (orderedInterval (-5527430569 / 1000000000000) (-5527423579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (313390521405873 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50272017811 / 1000000000000) (-50272017810 / 1000000000000), orderedInterval (-74501406551 / 1000000000000) (-74501406550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (850916228756619 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6246372779 / 1000000000000) (-6246372762 / 1000000000000), orderedInterval (54361924450 / 1000000000000) (54361924466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1161853363301163 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37241370960 / 1000000000000) (37241472181 / 1000000000000), orderedInterval (-28433405346 / 1000000000000) (-28433304125 / 1000000000000)))) (orderedInterval (3165543013 / 1000000000000) (3165552153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (491276713730481 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63545947030 / 1000000000000) (-63545947029 / 1000000000000), orderedInterval (-33583281435 / 1000000000000) (-33583281434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1997012566446801 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17899668010 / 1000000000000) (-17899668009 / 1000000000000), orderedInterval (-30881045278 / 1000000000000) (-30881045277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1333911844708959 / 4000000000000) 2 (IntervalRat.scale (537 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41520446862 / 1000000000000) (41520446864 / 1000000000000), orderedInterval (13542223043 / 1000000000000) (13542223045 / 1000000000000)))) (orderedInterval (7054312223 / 1000000000000) (7054312379 / 1000000000000))) = true
  rfl'

theorem compactCertificate397_chunkChecks2 :
    compactCertificate397.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate397.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate397_chunkChecks2_0
    compactCertificate397_chunkChecks2_1 compactCertificate397_chunkChecks2_2

theorem compactCertificate397_chunkChecks3_0 :
    compactCertificate397.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (537 / 2) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37900393016 / 1000000000000) (-37900305008 / 1000000000000), orderedInterval (30641530229 / 1000000000000) (30641618238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (791103539022837 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33896286283 / 1000000000000) (-33896286282 / 1000000000000), orderedInterval (-45410895163 / 1000000000000) (-45410895162 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (255826630272021 / 800000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5600142348 / 1000000000000) (5600142349 / 1000000000000), orderedInterval (44256645272 / 1000000000000) (44256645273 / 1000000000000)))) (orderedInterval (-16418033490 / 1000000000000) (-16417998448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (230842039646559 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97756945802 / 1000000000000) (97756948902 / 1000000000000), orderedInterval (-39246615516 / 1000000000000) (-39246612416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (620074189109523 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61328331024 / 1000000000000) (-61328328847 / 1000000000000), orderedInterval (18786811341 / 1000000000000) (18786813518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1683622045040391 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25561980456 / 1000000000000) (25561980457 / 1000000000000), orderedInterval (29279799090 / 1000000000000) (29279799091 / 1000000000000)))) (orderedInterval (7862633255 / 1000000000000) (7862633347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1240148378219583 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8806271003 / 1000000000000) (8806271029 / 1000000000000), orderedInterval (-44464382172 / 1000000000000) (-44464382145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2125015383731259 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31004061334 / 1000000000000) (-31004061332 / 1000000000000), orderedInterval (-15368296550 / 1000000000000) (-15368296549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1565276713730481 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22601854665 / 1000000000000) (22601857453 / 1000000000000), orderedInterval (-33435648132 / 1000000000000) (-33435645344 / 1000000000000)))) (orderedInterval (-1151901640 / 1000000000000) (-1151901345 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate397_chunkChecks3_1 :
    compactCertificate397.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2401537007834463 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29384042881 / 1000000000000) (-29384042879 / 1000000000000), orderedInterval (-14008763649 / 1000000000000) (-14008763647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1386528037941927 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41290653683 / 1000000000000) (41290658523 / 1000000000000), orderedInterval (-11534180672 / 1000000000000) (-11534175833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2460418334570643 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4413372407 / 1000000000000) (4413372408 / 1000000000000), orderedInterval (31863332211 / 1000000000000) (31863332212 / 1000000000000)))) (orderedInterval (-80321348814 / 1000000000000) (-80321346999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2298841965227967 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18356803777 / 1000000000000) (-18356803776 / 1000000000000), orderedInterval (-27746422654 / 1000000000000) (-27746422653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1640562098793711 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22988306137 / 1000000000000) (22988309555 / 1000000000000), orderedInterval (-32023920259 / 1000000000000) (-32023916842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1860222567328569 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28635285378 / 1000000000000) (28635285379 / 1000000000000), orderedInterval (23398494987 / 1000000000000) (23398494988 / 1000000000000)))) (orderedInterval (6519382363 / 1000000000000) (6519383664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1550859638686761 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35299465424 / 1000000000000) (-35299405617 / 1000000000000), orderedInterval (19943435378 / 1000000000000) (19943495185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1370231523633981 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34016966970 / 1000000000000) (-34016966969 / 1000000000000), orderedInterval (-26431951126 / 1000000000000) (-26431951125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (397146502888119 / 800000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26824012019 / 1000000000000) (26824012020 / 1000000000000), orderedInterval (23697655441 / 1000000000000) (23697655442 / 1000000000000)))) (orderedInterval (-7652129106 / 1000000000000) (-7652126935 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate397_chunkChecks3_2 :
    compactCertificate397.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1098528127663893 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41598966978 / 1000000000000) (-41598926010 / 1000000000000), orderedInterval (24316350404 / 1000000000000) (24316391372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (931234459686573 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46968325821 / 1000000000000) (46968325822 / 1000000000000), orderedInterval (22888088111 / 1000000000000) (22888088112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (582723286269519 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61357827520 / 1000000000000) (61357832829 / 1000000000000), orderedInterval (-24810607532 / 1000000000000) (-24810602222 / 1000000000000)))) (orderedInterval (5154517675 / 1000000000000) (5154524796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (313390521405873 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50272017811 / 1000000000000) (-50272017810 / 1000000000000), orderedInterval (-74501406551 / 1000000000000) (-74501406550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (850916228756619 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6246372779 / 1000000000000) (-6246372762 / 1000000000000), orderedInterval (54361924450 / 1000000000000) (54361924466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1161853363301163 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37241370960 / 1000000000000) (37241472181 / 1000000000000), orderedInterval (-28433405346 / 1000000000000) (-28433304125 / 1000000000000)))) (orderedInterval (-2191375070 / 1000000000000) (-2191365185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (491276713730481 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63545947030 / 1000000000000) (-63545947029 / 1000000000000), orderedInterval (-33583281435 / 1000000000000) (-33583281434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1997012566446801 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17899668010 / 1000000000000) (-17899668009 / 1000000000000), orderedInterval (-30881045278 / 1000000000000) (-30881045277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1333911844708959 / 4000000000000) 3 (IntervalRat.scale (537 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41520446862 / 1000000000000) (41520446864 / 1000000000000), orderedInterval (13542223043 / 1000000000000) (13542223045 / 1000000000000)))) (orderedInterval (-11299375606 / 1000000000000) (-11299375366 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate397_chunkChecks3 :
    compactCertificate397.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate397.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate397_chunkChecks3_0
    compactCertificate397_chunkChecks3_1 compactCertificate397_chunkChecks3_2

theorem compactCertificate397_chunkChecks4_0 :
    compactCertificate397.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (537 / 2) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37900393016 / 1000000000000) (-37900305008 / 1000000000000), orderedInterval (30641530229 / 1000000000000) (30641618238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (791103539022837 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33896286283 / 1000000000000) (-33896286282 / 1000000000000), orderedInterval (-45410895163 / 1000000000000) (-45410895162 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (255826630272021 / 800000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (5600142348 / 1000000000000) (5600142349 / 1000000000000), orderedInterval (44256645272 / 1000000000000) (44256645273 / 1000000000000)))) (orderedInterval (-14331656754 / 1000000000000) (-14331621579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (230842039646559 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97756945802 / 1000000000000) (97756948902 / 1000000000000), orderedInterval (-39246615516 / 1000000000000) (-39246612416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (620074189109523 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61328331024 / 1000000000000) (-61328328847 / 1000000000000), orderedInterval (18786811341 / 1000000000000) (18786813518 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1683622045040391 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25561980456 / 1000000000000) (25561980457 / 1000000000000), orderedInterval (29279799090 / 1000000000000) (29279799091 / 1000000000000)))) (orderedInterval (-11283486008 / 1000000000000) (-11283485881 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1240148378219583 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8806271003 / 1000000000000) (8806271029 / 1000000000000), orderedInterval (-44464382172 / 1000000000000) (-44464382145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2125015383731259 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31004061334 / 1000000000000) (-31004061332 / 1000000000000), orderedInterval (-15368296550 / 1000000000000) (-15368296549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1565276713730481 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22601854665 / 1000000000000) (22601857453 / 1000000000000), orderedInterval (-33435648132 / 1000000000000) (-33435645344 / 1000000000000)))) (orderedInterval (17129203569 / 1000000000000) (17129204033 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate397_chunkChecks4_1 :
    compactCertificate397.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2401537007834463 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29384042881 / 1000000000000) (-29384042879 / 1000000000000), orderedInterval (-14008763649 / 1000000000000) (-14008763647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1386528037941927 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (41290653683 / 1000000000000) (41290658523 / 1000000000000), orderedInterval (-11534180672 / 1000000000000) (-11534175833 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2460418334570643 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4413372407 / 1000000000000) (4413372408 / 1000000000000), orderedInterval (31863332211 / 1000000000000) (31863332212 / 1000000000000)))) (orderedInterval (156906019194 / 1000000000000) (156906022510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2298841965227967 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18356803777 / 1000000000000) (-18356803776 / 1000000000000), orderedInterval (-27746422654 / 1000000000000) (-27746422653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1640562098793711 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22988306137 / 1000000000000) (22988309555 / 1000000000000), orderedInterval (-32023920259 / 1000000000000) (-32023916842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1860222567328569 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28635285378 / 1000000000000) (28635285379 / 1000000000000), orderedInterval (23398494987 / 1000000000000) (23398494988 / 1000000000000)))) (orderedInterval (17438638425 / 1000000000000) (17438640447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1550859638686761 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35299465424 / 1000000000000) (-35299405617 / 1000000000000), orderedInterval (19943435378 / 1000000000000) (19943495185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1370231523633981 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34016966970 / 1000000000000) (-34016966969 / 1000000000000), orderedInterval (-26431951126 / 1000000000000) (-26431951125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (397146502888119 / 800000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26824012019 / 1000000000000) (26824012020 / 1000000000000), orderedInterval (23697655441 / 1000000000000) (23697655442 / 1000000000000)))) (orderedInterval (11468255052 / 1000000000000) (11468258206 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate397_chunkChecks4_2 :
    compactCertificate397.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1098528127663893 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41598966978 / 1000000000000) (-41598926010 / 1000000000000), orderedInterval (24316350404 / 1000000000000) (24316391372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (931234459686573 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46968325821 / 1000000000000) (46968325822 / 1000000000000), orderedInterval (22888088111 / 1000000000000) (22888088112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (582723286269519 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61357827520 / 1000000000000) (61357832829 / 1000000000000), orderedInterval (-24810607532 / 1000000000000) (-24810602222 / 1000000000000)))) (orderedInterval (5912155409 / 1000000000000) (5912162703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (313390521405873 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50272017811 / 1000000000000) (-50272017810 / 1000000000000), orderedInterval (-74501406551 / 1000000000000) (-74501406550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (850916228756619 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6246372779 / 1000000000000) (-6246372762 / 1000000000000), orderedInterval (54361924450 / 1000000000000) (54361924466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1161853363301163 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37241370960 / 1000000000000) (37241472181 / 1000000000000), orderedInterval (-28433405346 / 1000000000000) (-28433304125 / 1000000000000)))) (orderedInterval (-3830050747 / 1000000000000) (-3830040018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (491276713730481 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63545947030 / 1000000000000) (-63545947029 / 1000000000000), orderedInterval (-33583281435 / 1000000000000) (-33583281434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1997012566446801 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17899668010 / 1000000000000) (-17899668009 / 1000000000000), orderedInterval (-30881045278 / 1000000000000) (-30881045277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1333911844708959 / 4000000000000) 4 (IntervalRat.scale (537 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41520446862 / 1000000000000) (41520446864 / 1000000000000), orderedInterval (13542223043 / 1000000000000) (13542223045 / 1000000000000)))) (orderedInterval (-1052393005 / 1000000000000) (-1052392621 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate397_chunkChecks4 :
    compactCertificate397.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate397.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate397_chunkChecks4_0
    compactCertificate397_chunkChecks4_1 compactCertificate397_chunkChecks4_2

theorem compactCertificate397_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate397.chunkCheck r b = true :=
  compactCertificate397.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate397_chunkChecks0
    · exact compactCertificate397_chunkChecks1
    · exact compactCertificate397_chunkChecks2
    · exact compactCertificate397_chunkChecks3
    · exact compactCertificate397_chunkChecks4)

theorem compactCertificate397_coefficient0 :
    compactCertificate397.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate397_coefficient1 :
    compactCertificate397.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate397_coefficient2 :
    compactCertificate397.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate397_coefficient3 :
    compactCertificate397.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate397_coefficient4 :
    compactCertificate397.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate397_coefficients : ∀ r : Fin 5,
    compactCertificate397.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate397_coefficient0
  · exact compactCertificate397_coefficient1
  · exact compactCertificate397_coefficient2
  · exact compactCertificate397_coefficient3
  · exact compactCertificate397_coefficient4

theorem compactCertificate397_lower : (1 : ℚ) ≤ compactCertificate397.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate397, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate397_proves {t : ℝ} (ht : t ∈ compactCertificate397.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate397.proves compactCertificate397_states compactCertificate397_chunks
    compactCertificate397_coefficients compactCertificate397_lower ht

end Erdos232
