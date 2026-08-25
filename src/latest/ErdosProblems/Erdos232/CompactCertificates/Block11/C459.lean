/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate459 : CompactCertificate where
  left := 330
  right := 331
  center := 661 / 2
  grid := fun i =>
    match i.val with
    | 0 => 105
    | 1 => 78
    | 2 => 125
    | 3 => 23
    | 4 => 61
    | 5 => 165
    | 6 => 122
    | 7 => 208
    | 8 => 153
    | 9 => 235
    | 10 => 136
    | 11 => 241
    | 12 => 225
    | 13 => 161
    | 14 => 182
    | 15 => 152
    | 16 => 134
    | 17 => 195
    | 18 => 108
    | 19 => 91
    | 20 => 57
    | 21 => 31
    | 22 => 83
    | 23 => 114
    | 24 => 48
    | 25 => 196
    | _ => 131
  point := fun i =>
    match i.val with
    | 0 => 661 / 2
    | 1 => 973779216562561 / 4000000000000
    | 2 => 314900191079713 / 800000000000
    | 3 => 284146346753027 / 4000000000000
    | 4 => 763257055868519 / 4000000000000
    | 5 => 2072391381325323 / 4000000000000
    | 6 => 1526514111737699 / 4000000000000
    | 7 => 2615707949062127 / 4000000000000
    | 8 => 1926718636454093 / 4000000000000
    | 9 => 2956081866254339 / 4000000000000
    | 10 => 1706694661228331 / 4000000000000
    | 11 => 3028559625979879 / 4000000000000
    | 12 => 2829673257012451 / 4000000000000
    | 13 => 2019388356243283 / 4000000000000
    | 14 => 2289771167605557 / 4000000000000
    | 15 => 1908972478904933 / 4000000000000
    | 16 => 1686635078439593 / 4000000000000
    | 17 => 488852585491707 / 800000000000
    | 18 => 1352191978372129 / 4000000000000
    | 19 => 1146268115182169 / 4000000000000
    | 20 => 717281363545907 / 4000000000000
    | 21 => 385756302885069 / 4000000000000
    | 22 => 1047403402622207 / 4000000000000
    | 23 => 1430139801009439 / 4000000000000
    | 24 => 604718636454093 / 4000000000000
    | 25 => 2458147684211053 / 4000000000000
    | _ => 1641928732500227 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-43376108796 / 1000000000000) (-43376108777 / 1000000000000), orderedInterval (-6623427186 / 1000000000000) (-6623427167 / 1000000000000))
    | 1 => (orderedInterval (-37197876331 / 1000000000000) (-37197826003 / 1000000000000), orderedInterval (35167214246 / 1000000000000) (35167264574 / 1000000000000))
    | 2 => (orderedInterval (-39820004440 / 1000000000000) (-39820002950 / 1000000000000), orderedInterval (5680023031 / 1000000000000) (5680024521 / 1000000000000))
    | 3 => (orderedInterval (40013835798 / 1000000000000) (40013838666 / 1000000000000), orderedInterval (-86077276729 / 1000000000000) (-86077273861 / 1000000000000))
    | 4 => (orderedInterval (2202744382 / 1000000000000) (2202744388 / 1000000000000), orderedInterval (-57724846184 / 1000000000000) (-57724846178 / 1000000000000))
    | 5 => (orderedInterval (-17424016655 / 1000000000000) (-17424016654 / 1000000000000), orderedInterval (-30399751358 / 1000000000000) (-30399751357 / 1000000000000))
    | 6 => (orderedInterval (-30971497237 / 1000000000000) (-30971456474 / 1000000000000), orderedInterval (26666361588 / 1000000000000) (26666402352 / 1000000000000))
    | 7 => (orderedInterval (29715427748 / 1000000000000) (29715427769 / 1000000000000), orderedInterval (9491822611 / 1000000000000) (9491822632 / 1000000000000))
    | 8 => (orderedInterval (-35394672073 / 1000000000000) (-35394665615 / 1000000000000), orderedInterval (8336320181 / 1000000000000) (8336326639 / 1000000000000))
    | 9 => (orderedInterval (-29327500458 / 1000000000000) (-29327499048 / 1000000000000), orderedInterval (-1135506799 / 1000000000000) (-1135505389 / 1000000000000))
    | 10 => (orderedInterval (7756135555 / 1000000000000) (7756135556 / 1000000000000), orderedInterval (37831318183 / 1000000000000) (37831318184 / 1000000000000))
    | 11 => (orderedInterval (-20827568984 / 1000000000000) (-20827568983 / 1000000000000), orderedInterval (-20161334707 / 1000000000000) (-20161334706 / 1000000000000))
    | 12 => (orderedInterval (-29238444725 / 1000000000000) (-29238444618 / 1000000000000), orderedInterval (-6689996540 / 1000000000000) (-6689996433 / 1000000000000))
    | 13 => (orderedInterval (5803916624 / 1000000000000) (5803916628 / 1000000000000), orderedInterval (-35039020624 / 1000000000000) (-35039020620 / 1000000000000))
    | 14 => (orderedInterval (33136805139 / 1000000000000) (33136805336 / 1000000000000), orderedInterval (3721050865 / 1000000000000) (3721051062 / 1000000000000))
    | 15 => (orderedInterval (17707717994 / 1000000000000) (17707717995 / 1000000000000), orderedInterval (31924989718 / 1000000000000) (31924989719 / 1000000000000))
    | 16 => (orderedInterval (38660669655 / 1000000000000) (38660669737 / 1000000000000), orderedInterval (3846464962 / 1000000000000) (3846465043 / 1000000000000))
    | 17 => (orderedInterval (22228083967 / 1000000000000) (22228088923 / 1000000000000), orderedInterval (-23421843870 / 1000000000000) (-23421838914 / 1000000000000))
    | 18 => (orderedInterval (-19226081340 / 1000000000000) (-19226080546 / 1000000000000), orderedInterval (38933218966 / 1000000000000) (38933219760 / 1000000000000))
    | 19 => (orderedInterval (-46879785389 / 1000000000000) (-46879785360 / 1000000000000), orderedInterval (-4798902577 / 1000000000000) (-4798902549 / 1000000000000))
    | 20 => (orderedInterval (-51210921669 / 1000000000000) (-51210921668 / 1000000000000), orderedInterval (-30314006660 / 1000000000000) (-30314006659 / 1000000000000))
    | 21 => (orderedInterval (13440829544 / 1000000000000) (13440829627 / 1000000000000), orderedInterval (-80198902396 / 1000000000000) (-80198902312 / 1000000000000))
    | 22 => (orderedInterval (-46915084806 / 1000000000000) (-46915080025 / 1000000000000), orderedInterval (15261987750 / 1000000000000) (15261992531 / 1000000000000))
    | 23 => (orderedInterval (7489567098 / 1000000000000) (7489567099 / 1000000000000), orderedInterval (41516487841 / 1000000000000) (41516487842 / 1000000000000))
    | 24 => (orderedInterval (59693216025 / 1000000000000) (59693216026 / 1000000000000), orderedInterval (25252896693 / 1000000000000) (25252896694 / 1000000000000))
    | 25 => (orderedInterval (-13418668364 / 1000000000000) (-13418668278 / 1000000000000), orderedInterval (29266236778 / 1000000000000) (29266236864 / 1000000000000))
    | _ => (orderedInterval (10934807428 / 1000000000000) (10934807473 / 1000000000000), orderedInterval (-37846349441 / 1000000000000) (-37846349397 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-19876066370 / 1000000000000) (-19876065783 / 1000000000000)
      | 1 => orderedInterval (884971332 / 1000000000000) (884971404 / 1000000000000)
      | 2 => orderedInterval (-1771962084 / 1000000000000) (-1771961908 / 1000000000000)
      | 3 => orderedInterval (2825046587 / 1000000000000) (2825046969 / 1000000000000)
      | 4 => orderedInterval (908987803 / 1000000000000) (908987847 / 1000000000000)
      | 5 => orderedInterval (-1438812041 / 1000000000000) (-1438811878 / 1000000000000)
      | 6 => orderedInterval (4060313283 / 1000000000000) (4060313494 / 1000000000000)
      | 7 => orderedInterval (242177475 / 1000000000000) (242177625 / 1000000000000)
      | _ => orderedInterval (-599506267 / 1000000000000) (-599506160 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1986947339 / 1000000000000) (-1986946856 / 1000000000000)
      | 1 => orderedInterval (2371672440 / 1000000000000) (2371672492 / 1000000000000)
      | 2 => orderedInterval (-285634771 / 1000000000000) (-285634510 / 1000000000000)
      | 3 => orderedInterval (-2496012495 / 1000000000000) (-2496011663 / 1000000000000)
      | 4 => orderedInterval (-4835389974 / 1000000000000) (-4835389903 / 1000000000000)
      | 5 => orderedInterval (-857266810 / 1000000000000) (-857266523 / 1000000000000)
      | 6 => orderedInterval (-6667240612 / 1000000000000) (-6667240404 / 1000000000000)
      | 7 => orderedInterval (-3284255615 / 1000000000000) (-3284255492 / 1000000000000)
      | _ => orderedInterval (4459346480 / 1000000000000) (4459346632 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (20701381302 / 1000000000000) (20701381719 / 1000000000000)
      | 1 => orderedInterval (-3057863340 / 1000000000000) (-3057863276 / 1000000000000)
      | 2 => orderedInterval (5405985878 / 1000000000000) (5405986270 / 1000000000000)
      | 3 => orderedInterval (-11467305672 / 1000000000000) (-11467303835 / 1000000000000)
      | 4 => orderedInterval (-3181239567 / 1000000000000) (-3181239448 / 1000000000000)
      | 5 => orderedInterval (1231868893 / 1000000000000) (1231869403 / 1000000000000)
      | 6 => orderedInterval (-4700008348 / 1000000000000) (-4700008140 / 1000000000000)
      | 7 => orderedInterval (34691025 / 1000000000000) (34691129 / 1000000000000)
      | _ => orderedInterval (-700512286 / 1000000000000) (-700512059 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (1868579163 / 1000000000000) (1868579542 / 1000000000000)
      | 1 => orderedInterval (-7919635286 / 1000000000000) (-7919635191 / 1000000000000)
      | 2 => orderedInterval (1627681689 / 1000000000000) (1627682282 / 1000000000000)
      | 3 => orderedInterval (26206432226 / 1000000000000) (26206436308 / 1000000000000)
      | 4 => orderedInterval (10732716039 / 1000000000000) (10732716244 / 1000000000000)
      | 5 => orderedInterval (3133699435 / 1000000000000) (3133700353 / 1000000000000)
      | 6 => orderedInterval (6656181792 / 1000000000000) (6656182000 / 1000000000000)
      | 7 => orderedInterval (4163469969 / 1000000000000) (4163470061 / 1000000000000)
      | _ => orderedInterval (1698427987 / 1000000000000) (1698428341 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-22007527274 / 1000000000000) (-22007526909 / 1000000000000)
      | 1 => orderedInterval (7536152877 / 1000000000000) (7536153022 / 1000000000000)
      | 2 => orderedInterval (-17916269418 / 1000000000000) (-17916268508 / 1000000000000)
      | 3 => orderedInterval (50166505880 / 1000000000000) (50166514996 / 1000000000000)
      | 4 => orderedInterval (12493527115 / 1000000000000) (12493527478 / 1000000000000)
      | 5 => orderedInterval (1659179566 / 1000000000000) (1659181233 / 1000000000000)
      | 6 => orderedInterval (4679650829 / 1000000000000) (4679651040 / 1000000000000)
      | 7 => orderedInterval (-393734194 / 1000000000000) (-393734112 / 1000000000000)
      | _ => orderedInterval (8180660561 / 1000000000000) (8180661136 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-14764850282 / 1000000000000) (-14764848390 / 1000000000000)
    | 1 => orderedInterval (-13581728696 / 1000000000000) (-13581726227 / 1000000000000)
    | 2 => orderedInterval (4266997885 / 1000000000000) (4267001763 / 1000000000000)
    | 3 => orderedInterval (48167553014 / 1000000000000) (48167559940 / 1000000000000)
    | _ => orderedInterval (44398145942 / 1000000000000) (44398159376 / 1000000000000)

theorem compactCertificate459_stateChecks0 :
    compactCertificate459.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (661 / 2)) (orderedInterval (-43376108796 / 1000000000000) (-43376108777 / 1000000000000), orderedInterval (-6623427186 / 1000000000000) (-6623427167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (973779216562561 / 4000000000000)) (orderedInterval (-37197876331 / 1000000000000) (-37197826003 / 1000000000000), orderedInterval (35167214246 / 1000000000000) (35167264574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (314900191079713 / 800000000000)) (orderedInterval (-39820004440 / 1000000000000) (-39820002950 / 1000000000000), orderedInterval (5680023031 / 1000000000000) (5680024521 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_stateChecks1 :
    compactCertificate459.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (284146346753027 / 4000000000000)) (orderedInterval (40013835798 / 1000000000000) (40013838666 / 1000000000000), orderedInterval (-86077276729 / 1000000000000) (-86077273861 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (763257055868519 / 4000000000000)) (orderedInterval (2202744382 / 1000000000000) (2202744388 / 1000000000000), orderedInterval (-57724846184 / 1000000000000) (-57724846178 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2072391381325323 / 4000000000000)) (orderedInterval (-17424016655 / 1000000000000) (-17424016654 / 1000000000000), orderedInterval (-30399751358 / 1000000000000) (-30399751357 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_stateChecks2 :
    compactCertificate459.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1526514111737699 / 4000000000000)) (orderedInterval (-30971497237 / 1000000000000) (-30971456474 / 1000000000000), orderedInterval (26666361588 / 1000000000000) (26666402352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2615707949062127 / 4000000000000)) (orderedInterval (29715427748 / 1000000000000) (29715427769 / 1000000000000), orderedInterval (9491822611 / 1000000000000) (9491822632 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1926718636454093 / 4000000000000)) (orderedInterval (-35394672073 / 1000000000000) (-35394665615 / 1000000000000), orderedInterval (8336320181 / 1000000000000) (8336326639 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_stateChecks3 :
    compactCertificate459.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2956081866254339 / 4000000000000)) (orderedInterval (-29327500458 / 1000000000000) (-29327499048 / 1000000000000), orderedInterval (-1135506799 / 1000000000000) (-1135505389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1706694661228331 / 4000000000000)) (orderedInterval (7756135555 / 1000000000000) (7756135556 / 1000000000000), orderedInterval (37831318183 / 1000000000000) (37831318184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (3028559625979879 / 4000000000000)) (orderedInterval (-20827568984 / 1000000000000) (-20827568983 / 1000000000000), orderedInterval (-20161334707 / 1000000000000) (-20161334706 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_stateChecks4 :
    compactCertificate459.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2829673257012451 / 4000000000000)) (orderedInterval (-29238444725 / 1000000000000) (-29238444618 / 1000000000000), orderedInterval (-6689996540 / 1000000000000) (-6689996433 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2019388356243283 / 4000000000000)) (orderedInterval (5803916624 / 1000000000000) (5803916628 / 1000000000000), orderedInterval (-35039020624 / 1000000000000) (-35039020620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2289771167605557 / 4000000000000)) (orderedInterval (33136805139 / 1000000000000) (33136805336 / 1000000000000), orderedInterval (3721050865 / 1000000000000) (3721051062 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_stateChecks5 :
    compactCertificate459.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1908972478904933 / 4000000000000)) (orderedInterval (17707717994 / 1000000000000) (17707717995 / 1000000000000), orderedInterval (31924989718 / 1000000000000) (31924989719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1686635078439593 / 4000000000000)) (orderedInterval (38660669655 / 1000000000000) (38660669737 / 1000000000000), orderedInterval (3846464962 / 1000000000000) (3846465043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (488852585491707 / 800000000000)) (orderedInterval (22228083967 / 1000000000000) (22228088923 / 1000000000000), orderedInterval (-23421843870 / 1000000000000) (-23421838914 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_stateChecks6 :
    compactCertificate459.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1352191978372129 / 4000000000000)) (orderedInterval (-19226081340 / 1000000000000) (-19226080546 / 1000000000000), orderedInterval (38933218966 / 1000000000000) (38933219760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1146268115182169 / 4000000000000)) (orderedInterval (-46879785389 / 1000000000000) (-46879785360 / 1000000000000), orderedInterval (-4798902577 / 1000000000000) (-4798902549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717281363545907 / 4000000000000)) (orderedInterval (-51210921669 / 1000000000000) (-51210921668 / 1000000000000), orderedInterval (-30314006660 / 1000000000000) (-30314006659 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_stateChecks7 :
    compactCertificate459.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (385756302885069 / 4000000000000)) (orderedInterval (13440829544 / 1000000000000) (13440829627 / 1000000000000), orderedInterval (-80198902396 / 1000000000000) (-80198902312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1047403402622207 / 4000000000000)) (orderedInterval (-46915084806 / 1000000000000) (-46915080025 / 1000000000000), orderedInterval (15261987750 / 1000000000000) (15261992531 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1430139801009439 / 4000000000000)) (orderedInterval (7489567098 / 1000000000000) (7489567099 / 1000000000000), orderedInterval (41516487841 / 1000000000000) (41516487842 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_stateChecks8 :
    compactCertificate459.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (604718636454093 / 4000000000000)) (orderedInterval (59693216025 / 1000000000000) (59693216026 / 1000000000000), orderedInterval (25252896693 / 1000000000000) (25252896694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2458147684211053 / 4000000000000)) (orderedInterval (-13418668364 / 1000000000000) (-13418668278 / 1000000000000), orderedInterval (29266236778 / 1000000000000) (29266236864 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1641928732500227 / 4000000000000)) (orderedInterval (10934807428 / 1000000000000) (10934807473 / 1000000000000), orderedInterval (-37846349441 / 1000000000000) (-37846349397 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_states : ∀ j,
    BesselStateValid (compactCertificate459.point j) (compactCertificate459.state j) :=
  compactCertificate459.statesValid_of_checks3 compactCertificate459_stateChecks0
    compactCertificate459_stateChecks1 compactCertificate459_stateChecks2
    compactCertificate459_stateChecks3 compactCertificate459_stateChecks4
    compactCertificate459_stateChecks5 compactCertificate459_stateChecks6
    compactCertificate459_stateChecks7 compactCertificate459_stateChecks8

theorem compactCertificate459_chunkChecks0_0 :
    compactCertificate459.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (661 / 2) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43376108796 / 1000000000000) (-43376108777 / 1000000000000), orderedInterval (-6623427186 / 1000000000000) (-6623427167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (973779216562561 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37197876331 / 1000000000000) (-37197826003 / 1000000000000), orderedInterval (35167214246 / 1000000000000) (35167264574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (314900191079713 / 800000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39820004440 / 1000000000000) (-39820002950 / 1000000000000), orderedInterval (5680023031 / 1000000000000) (5680024521 / 1000000000000)))) (orderedInterval (-19876066370 / 1000000000000) (-19876065783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (284146346753027 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (40013835798 / 1000000000000) (40013838666 / 1000000000000), orderedInterval (-86077276729 / 1000000000000) (-86077273861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (763257055868519 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2202744382 / 1000000000000) (2202744388 / 1000000000000), orderedInterval (-57724846184 / 1000000000000) (-57724846178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2072391381325323 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17424016655 / 1000000000000) (-17424016654 / 1000000000000), orderedInterval (-30399751358 / 1000000000000) (-30399751357 / 1000000000000)))) (orderedInterval (884971332 / 1000000000000) (884971404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1526514111737699 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30971497237 / 1000000000000) (-30971456474 / 1000000000000), orderedInterval (26666361588 / 1000000000000) (26666402352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2615707949062127 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29715427748 / 1000000000000) (29715427769 / 1000000000000), orderedInterval (9491822611 / 1000000000000) (9491822632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1926718636454093 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35394672073 / 1000000000000) (-35394665615 / 1000000000000), orderedInterval (8336320181 / 1000000000000) (8336326639 / 1000000000000)))) (orderedInterval (-1771962084 / 1000000000000) (-1771961908 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks0_1 :
    compactCertificate459.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2956081866254339 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29327500458 / 1000000000000) (-29327499048 / 1000000000000), orderedInterval (-1135506799 / 1000000000000) (-1135505389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1706694661228331 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7756135555 / 1000000000000) (7756135556 / 1000000000000), orderedInterval (37831318183 / 1000000000000) (37831318184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3028559625979879 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20827568984 / 1000000000000) (-20827568983 / 1000000000000), orderedInterval (-20161334707 / 1000000000000) (-20161334706 / 1000000000000)))) (orderedInterval (2825046587 / 1000000000000) (2825046969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2829673257012451 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29238444725 / 1000000000000) (-29238444618 / 1000000000000), orderedInterval (-6689996540 / 1000000000000) (-6689996433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2019388356243283 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5803916624 / 1000000000000) (5803916628 / 1000000000000), orderedInterval (-35039020624 / 1000000000000) (-35039020620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2289771167605557 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33136805139 / 1000000000000) (33136805336 / 1000000000000), orderedInterval (3721050865 / 1000000000000) (3721051062 / 1000000000000)))) (orderedInterval (908987803 / 1000000000000) (908987847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1908972478904933 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17707717994 / 1000000000000) (17707717995 / 1000000000000), orderedInterval (31924989718 / 1000000000000) (31924989719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1686635078439593 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38660669655 / 1000000000000) (38660669737 / 1000000000000), orderedInterval (3846464962 / 1000000000000) (3846465043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (488852585491707 / 800000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22228083967 / 1000000000000) (22228088923 / 1000000000000), orderedInterval (-23421843870 / 1000000000000) (-23421838914 / 1000000000000)))) (orderedInterval (-1438812041 / 1000000000000) (-1438811878 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks0_2 :
    compactCertificate459.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1352191978372129 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19226081340 / 1000000000000) (-19226080546 / 1000000000000), orderedInterval (38933218966 / 1000000000000) (38933219760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1146268115182169 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46879785389 / 1000000000000) (-46879785360 / 1000000000000), orderedInterval (-4798902577 / 1000000000000) (-4798902549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (717281363545907 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51210921669 / 1000000000000) (-51210921668 / 1000000000000), orderedInterval (-30314006660 / 1000000000000) (-30314006659 / 1000000000000)))) (orderedInterval (4060313283 / 1000000000000) (4060313494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (385756302885069 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13440829544 / 1000000000000) (13440829627 / 1000000000000), orderedInterval (-80198902396 / 1000000000000) (-80198902312 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1047403402622207 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46915084806 / 1000000000000) (-46915080025 / 1000000000000), orderedInterval (15261987750 / 1000000000000) (15261992531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1430139801009439 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7489567098 / 1000000000000) (7489567099 / 1000000000000), orderedInterval (41516487841 / 1000000000000) (41516487842 / 1000000000000)))) (orderedInterval (242177475 / 1000000000000) (242177625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (604718636454093 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59693216025 / 1000000000000) (59693216026 / 1000000000000), orderedInterval (25252896693 / 1000000000000) (25252896694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2458147684211053 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13418668364 / 1000000000000) (-13418668278 / 1000000000000), orderedInterval (29266236778 / 1000000000000) (29266236864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1641928732500227 / 4000000000000) 0 (IntervalRat.scale (661 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10934807428 / 1000000000000) (10934807473 / 1000000000000), orderedInterval (-37846349441 / 1000000000000) (-37846349397 / 1000000000000)))) (orderedInterval (-599506267 / 1000000000000) (-599506160 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks0 :
    compactCertificate459.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate459.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate459_chunkChecks0_0
    compactCertificate459_chunkChecks0_1 compactCertificate459_chunkChecks0_2

theorem compactCertificate459_chunkChecks1_0 :
    compactCertificate459.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (661 / 2) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43376108796 / 1000000000000) (-43376108777 / 1000000000000), orderedInterval (-6623427186 / 1000000000000) (-6623427167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (973779216562561 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37197876331 / 1000000000000) (-37197826003 / 1000000000000), orderedInterval (35167214246 / 1000000000000) (35167264574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (314900191079713 / 800000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39820004440 / 1000000000000) (-39820002950 / 1000000000000), orderedInterval (5680023031 / 1000000000000) (5680024521 / 1000000000000)))) (orderedInterval (-1986947339 / 1000000000000) (-1986946856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (284146346753027 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (40013835798 / 1000000000000) (40013838666 / 1000000000000), orderedInterval (-86077276729 / 1000000000000) (-86077273861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (763257055868519 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2202744382 / 1000000000000) (2202744388 / 1000000000000), orderedInterval (-57724846184 / 1000000000000) (-57724846178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2072391381325323 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17424016655 / 1000000000000) (-17424016654 / 1000000000000), orderedInterval (-30399751358 / 1000000000000) (-30399751357 / 1000000000000)))) (orderedInterval (2371672440 / 1000000000000) (2371672492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1526514111737699 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30971497237 / 1000000000000) (-30971456474 / 1000000000000), orderedInterval (26666361588 / 1000000000000) (26666402352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2615707949062127 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29715427748 / 1000000000000) (29715427769 / 1000000000000), orderedInterval (9491822611 / 1000000000000) (9491822632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1926718636454093 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35394672073 / 1000000000000) (-35394665615 / 1000000000000), orderedInterval (8336320181 / 1000000000000) (8336326639 / 1000000000000)))) (orderedInterval (-285634771 / 1000000000000) (-285634510 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks1_1 :
    compactCertificate459.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2956081866254339 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29327500458 / 1000000000000) (-29327499048 / 1000000000000), orderedInterval (-1135506799 / 1000000000000) (-1135505389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1706694661228331 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7756135555 / 1000000000000) (7756135556 / 1000000000000), orderedInterval (37831318183 / 1000000000000) (37831318184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3028559625979879 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20827568984 / 1000000000000) (-20827568983 / 1000000000000), orderedInterval (-20161334707 / 1000000000000) (-20161334706 / 1000000000000)))) (orderedInterval (-2496012495 / 1000000000000) (-2496011663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2829673257012451 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29238444725 / 1000000000000) (-29238444618 / 1000000000000), orderedInterval (-6689996540 / 1000000000000) (-6689996433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2019388356243283 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5803916624 / 1000000000000) (5803916628 / 1000000000000), orderedInterval (-35039020624 / 1000000000000) (-35039020620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2289771167605557 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33136805139 / 1000000000000) (33136805336 / 1000000000000), orderedInterval (3721050865 / 1000000000000) (3721051062 / 1000000000000)))) (orderedInterval (-4835389974 / 1000000000000) (-4835389903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1908972478904933 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17707717994 / 1000000000000) (17707717995 / 1000000000000), orderedInterval (31924989718 / 1000000000000) (31924989719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1686635078439593 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38660669655 / 1000000000000) (38660669737 / 1000000000000), orderedInterval (3846464962 / 1000000000000) (3846465043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (488852585491707 / 800000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22228083967 / 1000000000000) (22228088923 / 1000000000000), orderedInterval (-23421843870 / 1000000000000) (-23421838914 / 1000000000000)))) (orderedInterval (-857266810 / 1000000000000) (-857266523 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks1_2 :
    compactCertificate459.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1352191978372129 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19226081340 / 1000000000000) (-19226080546 / 1000000000000), orderedInterval (38933218966 / 1000000000000) (38933219760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1146268115182169 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46879785389 / 1000000000000) (-46879785360 / 1000000000000), orderedInterval (-4798902577 / 1000000000000) (-4798902549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (717281363545907 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51210921669 / 1000000000000) (-51210921668 / 1000000000000), orderedInterval (-30314006660 / 1000000000000) (-30314006659 / 1000000000000)))) (orderedInterval (-6667240612 / 1000000000000) (-6667240404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (385756302885069 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13440829544 / 1000000000000) (13440829627 / 1000000000000), orderedInterval (-80198902396 / 1000000000000) (-80198902312 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1047403402622207 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46915084806 / 1000000000000) (-46915080025 / 1000000000000), orderedInterval (15261987750 / 1000000000000) (15261992531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1430139801009439 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7489567098 / 1000000000000) (7489567099 / 1000000000000), orderedInterval (41516487841 / 1000000000000) (41516487842 / 1000000000000)))) (orderedInterval (-3284255615 / 1000000000000) (-3284255492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (604718636454093 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59693216025 / 1000000000000) (59693216026 / 1000000000000), orderedInterval (25252896693 / 1000000000000) (25252896694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2458147684211053 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13418668364 / 1000000000000) (-13418668278 / 1000000000000), orderedInterval (29266236778 / 1000000000000) (29266236864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1641928732500227 / 4000000000000) 1 (IntervalRat.scale (661 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10934807428 / 1000000000000) (10934807473 / 1000000000000), orderedInterval (-37846349441 / 1000000000000) (-37846349397 / 1000000000000)))) (orderedInterval (4459346480 / 1000000000000) (4459346632 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks1 :
    compactCertificate459.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate459.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate459_chunkChecks1_0
    compactCertificate459_chunkChecks1_1 compactCertificate459_chunkChecks1_2

theorem compactCertificate459_chunkChecks2_0 :
    compactCertificate459.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (661 / 2) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43376108796 / 1000000000000) (-43376108777 / 1000000000000), orderedInterval (-6623427186 / 1000000000000) (-6623427167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (973779216562561 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37197876331 / 1000000000000) (-37197826003 / 1000000000000), orderedInterval (35167214246 / 1000000000000) (35167264574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (314900191079713 / 800000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39820004440 / 1000000000000) (-39820002950 / 1000000000000), orderedInterval (5680023031 / 1000000000000) (5680024521 / 1000000000000)))) (orderedInterval (20701381302 / 1000000000000) (20701381719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (284146346753027 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (40013835798 / 1000000000000) (40013838666 / 1000000000000), orderedInterval (-86077276729 / 1000000000000) (-86077273861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (763257055868519 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2202744382 / 1000000000000) (2202744388 / 1000000000000), orderedInterval (-57724846184 / 1000000000000) (-57724846178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2072391381325323 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17424016655 / 1000000000000) (-17424016654 / 1000000000000), orderedInterval (-30399751358 / 1000000000000) (-30399751357 / 1000000000000)))) (orderedInterval (-3057863340 / 1000000000000) (-3057863276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1526514111737699 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30971497237 / 1000000000000) (-30971456474 / 1000000000000), orderedInterval (26666361588 / 1000000000000) (26666402352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2615707949062127 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29715427748 / 1000000000000) (29715427769 / 1000000000000), orderedInterval (9491822611 / 1000000000000) (9491822632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1926718636454093 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35394672073 / 1000000000000) (-35394665615 / 1000000000000), orderedInterval (8336320181 / 1000000000000) (8336326639 / 1000000000000)))) (orderedInterval (5405985878 / 1000000000000) (5405986270 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks2_1 :
    compactCertificate459.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2956081866254339 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29327500458 / 1000000000000) (-29327499048 / 1000000000000), orderedInterval (-1135506799 / 1000000000000) (-1135505389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1706694661228331 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7756135555 / 1000000000000) (7756135556 / 1000000000000), orderedInterval (37831318183 / 1000000000000) (37831318184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3028559625979879 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20827568984 / 1000000000000) (-20827568983 / 1000000000000), orderedInterval (-20161334707 / 1000000000000) (-20161334706 / 1000000000000)))) (orderedInterval (-11467305672 / 1000000000000) (-11467303835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2829673257012451 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29238444725 / 1000000000000) (-29238444618 / 1000000000000), orderedInterval (-6689996540 / 1000000000000) (-6689996433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2019388356243283 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5803916624 / 1000000000000) (5803916628 / 1000000000000), orderedInterval (-35039020624 / 1000000000000) (-35039020620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2289771167605557 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33136805139 / 1000000000000) (33136805336 / 1000000000000), orderedInterval (3721050865 / 1000000000000) (3721051062 / 1000000000000)))) (orderedInterval (-3181239567 / 1000000000000) (-3181239448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1908972478904933 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17707717994 / 1000000000000) (17707717995 / 1000000000000), orderedInterval (31924989718 / 1000000000000) (31924989719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1686635078439593 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38660669655 / 1000000000000) (38660669737 / 1000000000000), orderedInterval (3846464962 / 1000000000000) (3846465043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (488852585491707 / 800000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22228083967 / 1000000000000) (22228088923 / 1000000000000), orderedInterval (-23421843870 / 1000000000000) (-23421838914 / 1000000000000)))) (orderedInterval (1231868893 / 1000000000000) (1231869403 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks2_2 :
    compactCertificate459.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1352191978372129 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19226081340 / 1000000000000) (-19226080546 / 1000000000000), orderedInterval (38933218966 / 1000000000000) (38933219760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1146268115182169 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46879785389 / 1000000000000) (-46879785360 / 1000000000000), orderedInterval (-4798902577 / 1000000000000) (-4798902549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (717281363545907 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51210921669 / 1000000000000) (-51210921668 / 1000000000000), orderedInterval (-30314006660 / 1000000000000) (-30314006659 / 1000000000000)))) (orderedInterval (-4700008348 / 1000000000000) (-4700008140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (385756302885069 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13440829544 / 1000000000000) (13440829627 / 1000000000000), orderedInterval (-80198902396 / 1000000000000) (-80198902312 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1047403402622207 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46915084806 / 1000000000000) (-46915080025 / 1000000000000), orderedInterval (15261987750 / 1000000000000) (15261992531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1430139801009439 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7489567098 / 1000000000000) (7489567099 / 1000000000000), orderedInterval (41516487841 / 1000000000000) (41516487842 / 1000000000000)))) (orderedInterval (34691025 / 1000000000000) (34691129 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (604718636454093 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59693216025 / 1000000000000) (59693216026 / 1000000000000), orderedInterval (25252896693 / 1000000000000) (25252896694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2458147684211053 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13418668364 / 1000000000000) (-13418668278 / 1000000000000), orderedInterval (29266236778 / 1000000000000) (29266236864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1641928732500227 / 4000000000000) 2 (IntervalRat.scale (661 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10934807428 / 1000000000000) (10934807473 / 1000000000000), orderedInterval (-37846349441 / 1000000000000) (-37846349397 / 1000000000000)))) (orderedInterval (-700512286 / 1000000000000) (-700512059 / 1000000000000))) = true
  rfl'

theorem compactCertificate459_chunkChecks2 :
    compactCertificate459.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate459.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate459_chunkChecks2_0
    compactCertificate459_chunkChecks2_1 compactCertificate459_chunkChecks2_2

theorem compactCertificate459_chunkChecks3_0 :
    compactCertificate459.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (661 / 2) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43376108796 / 1000000000000) (-43376108777 / 1000000000000), orderedInterval (-6623427186 / 1000000000000) (-6623427167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (973779216562561 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37197876331 / 1000000000000) (-37197826003 / 1000000000000), orderedInterval (35167214246 / 1000000000000) (35167264574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (314900191079713 / 800000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39820004440 / 1000000000000) (-39820002950 / 1000000000000), orderedInterval (5680023031 / 1000000000000) (5680024521 / 1000000000000)))) (orderedInterval (1868579163 / 1000000000000) (1868579542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (284146346753027 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (40013835798 / 1000000000000) (40013838666 / 1000000000000), orderedInterval (-86077276729 / 1000000000000) (-86077273861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (763257055868519 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2202744382 / 1000000000000) (2202744388 / 1000000000000), orderedInterval (-57724846184 / 1000000000000) (-57724846178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2072391381325323 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17424016655 / 1000000000000) (-17424016654 / 1000000000000), orderedInterval (-30399751358 / 1000000000000) (-30399751357 / 1000000000000)))) (orderedInterval (-7919635286 / 1000000000000) (-7919635191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1526514111737699 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30971497237 / 1000000000000) (-30971456474 / 1000000000000), orderedInterval (26666361588 / 1000000000000) (26666402352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2615707949062127 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29715427748 / 1000000000000) (29715427769 / 1000000000000), orderedInterval (9491822611 / 1000000000000) (9491822632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1926718636454093 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35394672073 / 1000000000000) (-35394665615 / 1000000000000), orderedInterval (8336320181 / 1000000000000) (8336326639 / 1000000000000)))) (orderedInterval (1627681689 / 1000000000000) (1627682282 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate459_chunkChecks3_1 :
    compactCertificate459.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2956081866254339 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29327500458 / 1000000000000) (-29327499048 / 1000000000000), orderedInterval (-1135506799 / 1000000000000) (-1135505389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1706694661228331 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7756135555 / 1000000000000) (7756135556 / 1000000000000), orderedInterval (37831318183 / 1000000000000) (37831318184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3028559625979879 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20827568984 / 1000000000000) (-20827568983 / 1000000000000), orderedInterval (-20161334707 / 1000000000000) (-20161334706 / 1000000000000)))) (orderedInterval (26206432226 / 1000000000000) (26206436308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2829673257012451 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29238444725 / 1000000000000) (-29238444618 / 1000000000000), orderedInterval (-6689996540 / 1000000000000) (-6689996433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2019388356243283 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5803916624 / 1000000000000) (5803916628 / 1000000000000), orderedInterval (-35039020624 / 1000000000000) (-35039020620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2289771167605557 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33136805139 / 1000000000000) (33136805336 / 1000000000000), orderedInterval (3721050865 / 1000000000000) (3721051062 / 1000000000000)))) (orderedInterval (10732716039 / 1000000000000) (10732716244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1908972478904933 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17707717994 / 1000000000000) (17707717995 / 1000000000000), orderedInterval (31924989718 / 1000000000000) (31924989719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1686635078439593 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38660669655 / 1000000000000) (38660669737 / 1000000000000), orderedInterval (3846464962 / 1000000000000) (3846465043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (488852585491707 / 800000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22228083967 / 1000000000000) (22228088923 / 1000000000000), orderedInterval (-23421843870 / 1000000000000) (-23421838914 / 1000000000000)))) (orderedInterval (3133699435 / 1000000000000) (3133700353 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate459_chunkChecks3_2 :
    compactCertificate459.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1352191978372129 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19226081340 / 1000000000000) (-19226080546 / 1000000000000), orderedInterval (38933218966 / 1000000000000) (38933219760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1146268115182169 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46879785389 / 1000000000000) (-46879785360 / 1000000000000), orderedInterval (-4798902577 / 1000000000000) (-4798902549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (717281363545907 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51210921669 / 1000000000000) (-51210921668 / 1000000000000), orderedInterval (-30314006660 / 1000000000000) (-30314006659 / 1000000000000)))) (orderedInterval (6656181792 / 1000000000000) (6656182000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (385756302885069 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13440829544 / 1000000000000) (13440829627 / 1000000000000), orderedInterval (-80198902396 / 1000000000000) (-80198902312 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1047403402622207 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46915084806 / 1000000000000) (-46915080025 / 1000000000000), orderedInterval (15261987750 / 1000000000000) (15261992531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1430139801009439 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7489567098 / 1000000000000) (7489567099 / 1000000000000), orderedInterval (41516487841 / 1000000000000) (41516487842 / 1000000000000)))) (orderedInterval (4163469969 / 1000000000000) (4163470061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (604718636454093 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59693216025 / 1000000000000) (59693216026 / 1000000000000), orderedInterval (25252896693 / 1000000000000) (25252896694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2458147684211053 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13418668364 / 1000000000000) (-13418668278 / 1000000000000), orderedInterval (29266236778 / 1000000000000) (29266236864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1641928732500227 / 4000000000000) 3 (IntervalRat.scale (661 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10934807428 / 1000000000000) (10934807473 / 1000000000000), orderedInterval (-37846349441 / 1000000000000) (-37846349397 / 1000000000000)))) (orderedInterval (1698427987 / 1000000000000) (1698428341 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate459_chunkChecks3 :
    compactCertificate459.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate459.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate459_chunkChecks3_0
    compactCertificate459_chunkChecks3_1 compactCertificate459_chunkChecks3_2

theorem compactCertificate459_chunkChecks4_0 :
    compactCertificate459.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (661 / 2) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43376108796 / 1000000000000) (-43376108777 / 1000000000000), orderedInterval (-6623427186 / 1000000000000) (-6623427167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (973779216562561 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37197876331 / 1000000000000) (-37197826003 / 1000000000000), orderedInterval (35167214246 / 1000000000000) (35167264574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (314900191079713 / 800000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39820004440 / 1000000000000) (-39820002950 / 1000000000000), orderedInterval (5680023031 / 1000000000000) (5680024521 / 1000000000000)))) (orderedInterval (-22007527274 / 1000000000000) (-22007526909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (284146346753027 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (40013835798 / 1000000000000) (40013838666 / 1000000000000), orderedInterval (-86077276729 / 1000000000000) (-86077273861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (763257055868519 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2202744382 / 1000000000000) (2202744388 / 1000000000000), orderedInterval (-57724846184 / 1000000000000) (-57724846178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2072391381325323 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17424016655 / 1000000000000) (-17424016654 / 1000000000000), orderedInterval (-30399751358 / 1000000000000) (-30399751357 / 1000000000000)))) (orderedInterval (7536152877 / 1000000000000) (7536153022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1526514111737699 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30971497237 / 1000000000000) (-30971456474 / 1000000000000), orderedInterval (26666361588 / 1000000000000) (26666402352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2615707949062127 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29715427748 / 1000000000000) (29715427769 / 1000000000000), orderedInterval (9491822611 / 1000000000000) (9491822632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1926718636454093 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35394672073 / 1000000000000) (-35394665615 / 1000000000000), orderedInterval (8336320181 / 1000000000000) (8336326639 / 1000000000000)))) (orderedInterval (-17916269418 / 1000000000000) (-17916268508 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate459_chunkChecks4_1 :
    compactCertificate459.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2956081866254339 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29327500458 / 1000000000000) (-29327499048 / 1000000000000), orderedInterval (-1135506799 / 1000000000000) (-1135505389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1706694661228331 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7756135555 / 1000000000000) (7756135556 / 1000000000000), orderedInterval (37831318183 / 1000000000000) (37831318184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3028559625979879 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20827568984 / 1000000000000) (-20827568983 / 1000000000000), orderedInterval (-20161334707 / 1000000000000) (-20161334706 / 1000000000000)))) (orderedInterval (50166505880 / 1000000000000) (50166514996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2829673257012451 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29238444725 / 1000000000000) (-29238444618 / 1000000000000), orderedInterval (-6689996540 / 1000000000000) (-6689996433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2019388356243283 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5803916624 / 1000000000000) (5803916628 / 1000000000000), orderedInterval (-35039020624 / 1000000000000) (-35039020620 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2289771167605557 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33136805139 / 1000000000000) (33136805336 / 1000000000000), orderedInterval (3721050865 / 1000000000000) (3721051062 / 1000000000000)))) (orderedInterval (12493527115 / 1000000000000) (12493527478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1908972478904933 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17707717994 / 1000000000000) (17707717995 / 1000000000000), orderedInterval (31924989718 / 1000000000000) (31924989719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1686635078439593 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38660669655 / 1000000000000) (38660669737 / 1000000000000), orderedInterval (3846464962 / 1000000000000) (3846465043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (488852585491707 / 800000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22228083967 / 1000000000000) (22228088923 / 1000000000000), orderedInterval (-23421843870 / 1000000000000) (-23421838914 / 1000000000000)))) (orderedInterval (1659179566 / 1000000000000) (1659181233 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate459_chunkChecks4_2 :
    compactCertificate459.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1352191978372129 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19226081340 / 1000000000000) (-19226080546 / 1000000000000), orderedInterval (38933218966 / 1000000000000) (38933219760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1146268115182169 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46879785389 / 1000000000000) (-46879785360 / 1000000000000), orderedInterval (-4798902577 / 1000000000000) (-4798902549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (717281363545907 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51210921669 / 1000000000000) (-51210921668 / 1000000000000), orderedInterval (-30314006660 / 1000000000000) (-30314006659 / 1000000000000)))) (orderedInterval (4679650829 / 1000000000000) (4679651040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (385756302885069 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (13440829544 / 1000000000000) (13440829627 / 1000000000000), orderedInterval (-80198902396 / 1000000000000) (-80198902312 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1047403402622207 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46915084806 / 1000000000000) (-46915080025 / 1000000000000), orderedInterval (15261987750 / 1000000000000) (15261992531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1430139801009439 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7489567098 / 1000000000000) (7489567099 / 1000000000000), orderedInterval (41516487841 / 1000000000000) (41516487842 / 1000000000000)))) (orderedInterval (-393734194 / 1000000000000) (-393734112 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (604718636454093 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59693216025 / 1000000000000) (59693216026 / 1000000000000), orderedInterval (25252896693 / 1000000000000) (25252896694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2458147684211053 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13418668364 / 1000000000000) (-13418668278 / 1000000000000), orderedInterval (29266236778 / 1000000000000) (29266236864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1641928732500227 / 4000000000000) 4 (IntervalRat.scale (661 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10934807428 / 1000000000000) (10934807473 / 1000000000000), orderedInterval (-37846349441 / 1000000000000) (-37846349397 / 1000000000000)))) (orderedInterval (8180660561 / 1000000000000) (8180661136 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate459_chunkChecks4 :
    compactCertificate459.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate459.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate459_chunkChecks4_0
    compactCertificate459_chunkChecks4_1 compactCertificate459_chunkChecks4_2

theorem compactCertificate459_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate459.chunkCheck r b = true :=
  compactCertificate459.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate459_chunkChecks0
    · exact compactCertificate459_chunkChecks1
    · exact compactCertificate459_chunkChecks2
    · exact compactCertificate459_chunkChecks3
    · exact compactCertificate459_chunkChecks4)

theorem compactCertificate459_coefficient0 :
    compactCertificate459.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate459_coefficient1 :
    compactCertificate459.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate459_coefficient2 :
    compactCertificate459.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate459_coefficient3 :
    compactCertificate459.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate459_coefficient4 :
    compactCertificate459.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate459_coefficients : ∀ r : Fin 5,
    compactCertificate459.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate459_coefficient0
  · exact compactCertificate459_coefficient1
  · exact compactCertificate459_coefficient2
  · exact compactCertificate459_coefficient3
  · exact compactCertificate459_coefficient4

theorem compactCertificate459_lower : (1 : ℚ) ≤ compactCertificate459.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate459, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate459_proves {t : ℝ} (ht : t ∈ compactCertificate459.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate459.proves compactCertificate459_states compactCertificate459_chunks
    compactCertificate459_coefficients compactCertificate459_lower ht

end Erdos232
