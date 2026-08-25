/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate590 : CompactCertificate where
  left := 461
  right := 462
  center := 923 / 2
  grid := fun i =>
    match i.val with
    | 0 => 147
    | 1 => 108
    | 2 => 175
    | 3 => 32
    | 4 => 85
    | 5 => 230
    | 6 => 170
    | 7 => 291
    | 8 => 214
    | 9 => 329
    | 10 => 190
    | 11 => 337
    | 12 => 315
    | 13 => 225
    | 14 => 255
    | 15 => 212
    | 16 => 188
    | 17 => 272
    | 18 => 150
    | 19 => 127
    | 20 => 80
    | 21 => 43
    | 22 => 116
    | 23 => 159
    | 24 => 67
    | 25 => 273
    | _ => 183
  point := fun i =>
    match i.val with
    | 0 => 923 / 2
    | 1 => 1359755244912623 / 4000000000000
    | 2 => 439716908270159 / 800000000000
    | 3 => 396773189187661 / 4000000000000
    | 4 => 1065788596923817 / 4000000000000
    | 5 => 2893823366056389 / 4000000000000
    | 6 => 2131577193848557 / 4000000000000
    | 7 => 3652493853228961 / 4000000000000
    | 8 => 2690410440918499 / 4000000000000
    | 9 => 4127781486464077 / 4000000000000
    | 10 => 2383175752365733 / 4000000000000
    | 11 => 4228987193312297 / 4000000000000
    | 12 => 3951268405782893 / 4000000000000
    | 13 => 2819811577628669 / 4000000000000
    | 14 => 3197365790771451 / 4000000000000
    | 15 => 2665630254204619 / 4000000000000
    | 16 => 2355165170044999 / 4000000000000
    | 17 => 682618663250901 / 800000000000
    | 18 => 1888159146804047 / 4000000000000
    | 19 => 1600613419535767 / 4000000000000
    | 20 => 1001589559081501 / 4000000000000
    | 21 => 538658196010467 / 4000000000000
    | 22 => 1462561786112401 / 4000000000000
    | 23 => 1997003080683377 / 4000000000000
    | 24 => 844410440918499 / 4000000000000
    | 25 => 3432481562067779 / 4000000000000
    | _ => 2292738608317261 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-16854013117 / 1000000000000) (-16854013116 / 1000000000000), orderedInterval (-33078575378 / 1000000000000) (-33078575377 / 1000000000000))
    | 1 => (orderedInterval (42858081239 / 1000000000000) (42858081264 / 1000000000000), orderedInterval (5931213721 / 1000000000000) (5931213746 / 1000000000000))
    | 2 => (orderedInterval (-20666368947 / 1000000000000) (-20666368946 / 1000000000000), orderedInterval (-27020745671 / 1000000000000) (-27020745670 / 1000000000000))
    | 3 => (orderedInterval (-42114182373 / 1000000000000) (-42114173861 / 1000000000000), orderedInterval (68362138665 / 1000000000000) (68362147176 / 1000000000000))
    | 4 => (orderedInterval (-9553010117 / 1000000000000) (-9553010116 / 1000000000000), orderedInterval (-47919896380 / 1000000000000) (-47919896379 / 1000000000000))
    | 5 => (orderedInterval (29504131843 / 1000000000000) (29504138051 / 1000000000000), orderedInterval (-3098749964 / 1000000000000) (-3098743756 / 1000000000000))
    | 6 => (orderedInterval (-13181892007 / 1000000000000) (-13181891917 / 1000000000000), orderedInterval (31963637154 / 1000000000000) (31963637243 / 1000000000000))
    | 7 => (orderedInterval (7670164125 / 1000000000000) (7670164127 / 1000000000000), orderedInterval (-25269943970 / 1000000000000) (-25269943969 / 1000000000000))
    | 8 => (orderedInterval (27234431908 / 1000000000000) (27234431910 / 1000000000000), orderedInterval (14290158162 / 1000000000000) (14290158164 / 1000000000000))
    | 9 => (orderedInterval (18714644690 / 1000000000000) (18714646008 / 1000000000000), orderedInterval (-16339234239 / 1000000000000) (-16339232921 / 1000000000000))
    | 10 => (orderedInterval (-10390484519 / 1000000000000) (-10390484499 / 1000000000000), orderedInterval (31001647190 / 1000000000000) (31001647210 / 1000000000000))
    | 11 => (orderedInterval (15518255642 / 1000000000000) (15518255774 / 1000000000000), orderedInterval (-19016085494 / 1000000000000) (-19016085363 / 1000000000000))
    | 12 => (orderedInterval (21352515784 / 1000000000000) (21352523975 / 1000000000000), orderedInterval (-13741840991 / 1000000000000) (-13741832801 / 1000000000000))
    | 13 => (orderedInterval (27051968676 / 1000000000000) (27052062112 / 1000000000000), orderedInterval (-13105690480 / 1000000000000) (-13105597044 / 1000000000000))
    | 14 => (orderedInterval (23428684899 / 1000000000000) (23428702148 / 1000000000000), orderedInterval (-15747640990 / 1000000000000) (-15747623740 / 1000000000000))
    | 15 => (orderedInterval (28520008642 / 1000000000000) (28520008649 / 1000000000000), orderedInterval (11891194123 / 1000000000000) (11891194130 / 1000000000000))
    | 16 => (orderedInterval (-28406508004 / 1000000000000) (-28406428026 / 1000000000000), orderedInterval (16586206154 / 1000000000000) (16586286132 / 1000000000000))
    | 17 => (orderedInterval (-11994468742 / 1000000000000) (-11994468721 / 1000000000000), orderedInterval (24547282310 / 1000000000000) (24547282331 / 1000000000000))
    | 18 => (orderedInterval (36719798751 / 1000000000000) (36719799285 / 1000000000000), orderedInterval (-598022886 / 1000000000000) (-598022352 / 1000000000000))
    | 19 => (orderedInterval (-36961162566 / 1000000000000) (-36961142708 / 1000000000000), orderedInterval (15039897750 / 1000000000000) (15039917608 / 1000000000000))
    | 20 => (orderedInterval (-7291840067 / 1000000000000) (-7291840048 / 1000000000000), orderedInterval (49907161719 / 1000000000000) (49907161738 / 1000000000000))
    | 21 => (orderedInterval (-24255454707 / 1000000000000) (-24255454706 / 1000000000000), orderedInterval (-64246139703 / 1000000000000) (-64246139702 / 1000000000000))
    | 22 => (orderedInterval (37928733385 / 1000000000000) (37928758984 / 1000000000000), orderedInterval (-17444918726 / 1000000000000) (-17444893126 / 1000000000000))
    | 23 => (orderedInterval (-17826385000 / 1000000000000) (-17826384999 / 1000000000000), orderedInterval (-30923553194 / 1000000000000) (-30923553193 / 1000000000000))
    | 24 => (orderedInterval (-54122778345 / 1000000000000) (-54122778340 / 1000000000000), orderedInterval (-9167274907 / 1000000000000) (-9167274902 / 1000000000000))
    | 25 => (orderedInterval (-25855168289 / 1000000000000) (-25855168206 / 1000000000000), orderedInterval (-8551565879 / 1000000000000) (-8551565796 / 1000000000000))
    | _ => (orderedInterval (26945127020 / 1000000000000) (26945162274 / 1000000000000), orderedInterval (-19635517786 / 1000000000000) (-19635482533 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-7493712724 / 1000000000000) (-7493712691 / 1000000000000)
      | 1 => orderedInterval (-1989326761 / 1000000000000) (-1989326172 / 1000000000000)
      | 2 => orderedInterval (421623922 / 1000000000000) (421623949 / 1000000000000)
      | 3 => orderedInterval (-1889204653 / 1000000000000) (-1889204216 / 1000000000000)
      | 4 => orderedInterval (2054069982 / 1000000000000) (2054079108 / 1000000000000)
      | 5 => orderedInterval (1647839329 / 1000000000000) (1647843951 / 1000000000000)
      | 6 => orderedInterval (-4016607214 / 1000000000000) (-4016605888 / 1000000000000)
      | 7 => orderedInterval (953589263 / 1000000000000) (953589899 / 1000000000000)
      | _ => orderedInterval (-3277240504 / 1000000000000) (-3277233755 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14958937661 / 1000000000000) (-14958937624 / 1000000000000)
      | 1 => orderedInterval (-824240665 / 1000000000000) (-824239890 / 1000000000000)
      | 2 => orderedInterval (2045516082 / 1000000000000) (2045516128 / 1000000000000)
      | 3 => orderedInterval (3264461280 / 1000000000000) (3264462227 / 1000000000000)
      | 4 => orderedInterval (-1224041334 / 1000000000000) (-1224027280 / 1000000000000)
      | 5 => orderedInterval (149358521 / 1000000000000) (149364426 / 1000000000000)
      | 6 => orderedInterval (241241608 / 1000000000000) (241242778 / 1000000000000)
      | 7 => orderedInterval (3223534460 / 1000000000000) (3223534970 / 1000000000000)
      | _ => orderedInterval (5844795654 / 1000000000000) (5844804061 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (8216302388 / 1000000000000) (8216302430 / 1000000000000)
      | 1 => orderedInterval (5251244806 / 1000000000000) (5251245984 / 1000000000000)
      | 2 => orderedInterval (-476345630 / 1000000000000) (-476345549 / 1000000000000)
      | 3 => orderedInterval (6325278293 / 1000000000000) (6325280379 / 1000000000000)
      | 4 => orderedInterval (-3844528574 / 1000000000000) (-3844506840 / 1000000000000)
      | 5 => orderedInterval (-2283246043 / 1000000000000) (-2283238483 / 1000000000000)
      | 6 => orderedInterval (4639024559 / 1000000000000) (4639025598 / 1000000000000)
      | 7 => orderedInterval (-1103823493 / 1000000000000) (-1103823078 / 1000000000000)
      | _ => orderedInterval (577569995 / 1000000000000) (577580505 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15749965905 / 1000000000000) (15749965954 / 1000000000000)
      | 1 => orderedInterval (-515920883 / 1000000000000) (-515919049 / 1000000000000)
      | 2 => orderedInterval (-7105486750 / 1000000000000) (-7105486604 / 1000000000000)
      | 3 => orderedInterval (-4914441146 / 1000000000000) (-4914436517 / 1000000000000)
      | 4 => orderedInterval (1578561834 / 1000000000000) (1578595526 / 1000000000000)
      | 5 => orderedInterval (-2409838651 / 1000000000000) (-2409828980 / 1000000000000)
      | 6 => orderedInterval (183028469 / 1000000000000) (183029394 / 1000000000000)
      | 7 => orderedInterval (-3224300284 / 1000000000000) (-3224299943 / 1000000000000)
      | _ => orderedInterval (-11529481929 / 1000000000000) (-11529468782 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9071099173 / 1000000000000) (-9071099115 / 1000000000000)
      | 1 => orderedInterval (-12701842189 / 1000000000000) (-12701839315 / 1000000000000)
      | 2 => orderedInterval (-625370902 / 1000000000000) (-625370631 / 1000000000000)
      | 3 => orderedInterval (-24490094621 / 1000000000000) (-24490084280 / 1000000000000)
      | 4 => orderedInterval (4762241229 / 1000000000000) (4762293802 / 1000000000000)
      | 5 => orderedInterval (2160498286 / 1000000000000) (2160510693 / 1000000000000)
      | 6 => orderedInterval (-5265123958 / 1000000000000) (-5265123128 / 1000000000000)
      | 7 => orderedInterval (1549272781 / 1000000000000) (1549273065 / 1000000000000)
      | _ => orderedInterval (13164309847 / 1000000000000) (13164326379 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13588969360 / 1000000000000) (-13588945815 / 1000000000000)
    | 1 => orderedInterval (-2238312055 / 1000000000000) (-2238280204 / 1000000000000)
    | 2 => orderedInterval (17301476301 / 1000000000000) (17301520946 / 1000000000000)
    | 3 => orderedInterval (-12187913435 / 1000000000000) (-12187849001 / 1000000000000)
    | _ => orderedInterval (-30517208700 / 1000000000000) (-30517112530 / 1000000000000)

theorem compactCertificate590_stateChecks0 :
    compactCertificate590.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (923 / 2)) (orderedInterval (-16854013117 / 1000000000000) (-16854013116 / 1000000000000), orderedInterval (-33078575378 / 1000000000000) (-33078575377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1359755244912623 / 4000000000000)) (orderedInterval (42858081239 / 1000000000000) (42858081264 / 1000000000000), orderedInterval (5931213721 / 1000000000000) (5931213746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (439716908270159 / 800000000000)) (orderedInterval (-20666368947 / 1000000000000) (-20666368946 / 1000000000000), orderedInterval (-27020745671 / 1000000000000) (-27020745670 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_stateChecks1 :
    compactCertificate590.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (396773189187661 / 4000000000000)) (orderedInterval (-42114182373 / 1000000000000) (-42114173861 / 1000000000000), orderedInterval (68362138665 / 1000000000000) (68362147176 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1065788596923817 / 4000000000000)) (orderedInterval (-9553010117 / 1000000000000) (-9553010116 / 1000000000000), orderedInterval (-47919896380 / 1000000000000) (-47919896379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2893823366056389 / 4000000000000)) (orderedInterval (29504131843 / 1000000000000) (29504138051 / 1000000000000), orderedInterval (-3098749964 / 1000000000000) (-3098743756 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_stateChecks2 :
    compactCertificate590.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2131577193848557 / 4000000000000)) (orderedInterval (-13181892007 / 1000000000000) (-13181891917 / 1000000000000), orderedInterval (31963637154 / 1000000000000) (31963637243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (3652493853228961 / 4000000000000)) (orderedInterval (7670164125 / 1000000000000) (7670164127 / 1000000000000), orderedInterval (-25269943970 / 1000000000000) (-25269943969 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2690410440918499 / 4000000000000)) (orderedInterval (27234431908 / 1000000000000) (27234431910 / 1000000000000), orderedInterval (14290158162 / 1000000000000) (14290158164 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_stateChecks3 :
    compactCertificate590.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 329 12 (4127781486464077 / 4000000000000)) (orderedInterval (18714644690 / 1000000000000) (18714646008 / 1000000000000), orderedInterval (-16339234239 / 1000000000000) (-16339232921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2383175752365733 / 4000000000000)) (orderedInterval (-10390484519 / 1000000000000) (-10390484499 / 1000000000000), orderedInterval (31001647190 / 1000000000000) (31001647210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 337 12 (4228987193312297 / 4000000000000)) (orderedInterval (15518255642 / 1000000000000) (15518255774 / 1000000000000), orderedInterval (-19016085494 / 1000000000000) (-19016085363 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_stateChecks4 :
    compactCertificate590.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 315 12 (3951268405782893 / 4000000000000)) (orderedInterval (21352515784 / 1000000000000) (21352523975 / 1000000000000), orderedInterval (-13741840991 / 1000000000000) (-13741832801 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2819811577628669 / 4000000000000)) (orderedInterval (27051968676 / 1000000000000) (27052062112 / 1000000000000), orderedInterval (-13105690480 / 1000000000000) (-13105597044 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (3197365790771451 / 4000000000000)) (orderedInterval (23428684899 / 1000000000000) (23428702148 / 1000000000000), orderedInterval (-15747640990 / 1000000000000) (-15747623740 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_stateChecks5 :
    compactCertificate590.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2665630254204619 / 4000000000000)) (orderedInterval (28520008642 / 1000000000000) (28520008649 / 1000000000000), orderedInterval (11891194123 / 1000000000000) (11891194130 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2355165170044999 / 4000000000000)) (orderedInterval (-28406508004 / 1000000000000) (-28406428026 / 1000000000000), orderedInterval (16586206154 / 1000000000000) (16586286132 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (682618663250901 / 800000000000)) (orderedInterval (-11994468742 / 1000000000000) (-11994468721 / 1000000000000), orderedInterval (24547282310 / 1000000000000) (24547282331 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_stateChecks6 :
    compactCertificate590.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1888159146804047 / 4000000000000)) (orderedInterval (36719798751 / 1000000000000) (36719799285 / 1000000000000), orderedInterval (-598022886 / 1000000000000) (-598022352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1600613419535767 / 4000000000000)) (orderedInterval (-36961162566 / 1000000000000) (-36961142708 / 1000000000000), orderedInterval (15039897750 / 1000000000000) (15039917608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1001589559081501 / 4000000000000)) (orderedInterval (-7291840067 / 1000000000000) (-7291840048 / 1000000000000), orderedInterval (49907161719 / 1000000000000) (49907161738 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_stateChecks7 :
    compactCertificate590.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (538658196010467 / 4000000000000)) (orderedInterval (-24255454707 / 1000000000000) (-24255454706 / 1000000000000), orderedInterval (-64246139703 / 1000000000000) (-64246139702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1462561786112401 / 4000000000000)) (orderedInterval (37928733385 / 1000000000000) (37928758984 / 1000000000000), orderedInterval (-17444918726 / 1000000000000) (-17444893126 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1997003080683377 / 4000000000000)) (orderedInterval (-17826385000 / 1000000000000) (-17826384999 / 1000000000000), orderedInterval (-30923553194 / 1000000000000) (-30923553193 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_stateChecks8 :
    compactCertificate590.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844410440918499 / 4000000000000)) (orderedInterval (-54122778345 / 1000000000000) (-54122778340 / 1000000000000), orderedInterval (-9167274907 / 1000000000000) (-9167274902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (3432481562067779 / 4000000000000)) (orderedInterval (-25855168289 / 1000000000000) (-25855168206 / 1000000000000), orderedInterval (-8551565879 / 1000000000000) (-8551565796 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2292738608317261 / 4000000000000)) (orderedInterval (26945127020 / 1000000000000) (26945162274 / 1000000000000), orderedInterval (-19635517786 / 1000000000000) (-19635482533 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_states : ∀ j,
    BesselStateValid (compactCertificate590.point j) (compactCertificate590.state j) :=
  compactCertificate590.statesValid_of_checks3 compactCertificate590_stateChecks0
    compactCertificate590_stateChecks1 compactCertificate590_stateChecks2
    compactCertificate590_stateChecks3 compactCertificate590_stateChecks4
    compactCertificate590_stateChecks5 compactCertificate590_stateChecks6
    compactCertificate590_stateChecks7 compactCertificate590_stateChecks8

theorem compactCertificate590_chunkChecks0_0 :
    compactCertificate590.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (923 / 2) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-16854013117 / 1000000000000) (-16854013116 / 1000000000000), orderedInterval (-33078575378 / 1000000000000) (-33078575377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1359755244912623 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42858081239 / 1000000000000) (42858081264 / 1000000000000), orderedInterval (5931213721 / 1000000000000) (5931213746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (439716908270159 / 800000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20666368947 / 1000000000000) (-20666368946 / 1000000000000), orderedInterval (-27020745671 / 1000000000000) (-27020745670 / 1000000000000)))) (orderedInterval (-7493712724 / 1000000000000) (-7493712691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (396773189187661 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-42114182373 / 1000000000000) (-42114173861 / 1000000000000), orderedInterval (68362138665 / 1000000000000) (68362147176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1065788596923817 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9553010117 / 1000000000000) (-9553010116 / 1000000000000), orderedInterval (-47919896380 / 1000000000000) (-47919896379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2893823366056389 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29504131843 / 1000000000000) (29504138051 / 1000000000000), orderedInterval (-3098749964 / 1000000000000) (-3098743756 / 1000000000000)))) (orderedInterval (-1989326761 / 1000000000000) (-1989326172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2131577193848557 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13181892007 / 1000000000000) (-13181891917 / 1000000000000), orderedInterval (31963637154 / 1000000000000) (31963637243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3652493853228961 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7670164125 / 1000000000000) (7670164127 / 1000000000000), orderedInterval (-25269943970 / 1000000000000) (-25269943969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2690410440918499 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27234431908 / 1000000000000) (27234431910 / 1000000000000), orderedInterval (14290158162 / 1000000000000) (14290158164 / 1000000000000)))) (orderedInterval (421623922 / 1000000000000) (421623949 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks0_1 :
    compactCertificate590.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4127781486464077 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18714644690 / 1000000000000) (18714646008 / 1000000000000), orderedInterval (-16339234239 / 1000000000000) (-16339232921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2383175752365733 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10390484519 / 1000000000000) (-10390484499 / 1000000000000), orderedInterval (31001647190 / 1000000000000) (31001647210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4228987193312297 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15518255642 / 1000000000000) (15518255774 / 1000000000000), orderedInterval (-19016085494 / 1000000000000) (-19016085363 / 1000000000000)))) (orderedInterval (-1889204653 / 1000000000000) (-1889204216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3951268405782893 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21352515784 / 1000000000000) (21352523975 / 1000000000000), orderedInterval (-13741840991 / 1000000000000) (-13741832801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2819811577628669 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27051968676 / 1000000000000) (27052062112 / 1000000000000), orderedInterval (-13105690480 / 1000000000000) (-13105597044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3197365790771451 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23428684899 / 1000000000000) (23428702148 / 1000000000000), orderedInterval (-15747640990 / 1000000000000) (-15747623740 / 1000000000000)))) (orderedInterval (2054069982 / 1000000000000) (2054079108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2665630254204619 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28520008642 / 1000000000000) (28520008649 / 1000000000000), orderedInterval (11891194123 / 1000000000000) (11891194130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2355165170044999 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28406508004 / 1000000000000) (-28406428026 / 1000000000000), orderedInterval (16586206154 / 1000000000000) (16586286132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (682618663250901 / 800000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11994468742 / 1000000000000) (-11994468721 / 1000000000000), orderedInterval (24547282310 / 1000000000000) (24547282331 / 1000000000000)))) (orderedInterval (1647839329 / 1000000000000) (1647843951 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks0_2 :
    compactCertificate590.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1888159146804047 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36719798751 / 1000000000000) (36719799285 / 1000000000000), orderedInterval (-598022886 / 1000000000000) (-598022352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1600613419535767 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36961162566 / 1000000000000) (-36961142708 / 1000000000000), orderedInterval (15039897750 / 1000000000000) (15039917608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1001589559081501 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7291840067 / 1000000000000) (-7291840048 / 1000000000000), orderedInterval (49907161719 / 1000000000000) (49907161738 / 1000000000000)))) (orderedInterval (-4016607214 / 1000000000000) (-4016605888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (538658196010467 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-24255454707 / 1000000000000) (-24255454706 / 1000000000000), orderedInterval (-64246139703 / 1000000000000) (-64246139702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1462561786112401 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37928733385 / 1000000000000) (37928758984 / 1000000000000), orderedInterval (-17444918726 / 1000000000000) (-17444893126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1997003080683377 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17826385000 / 1000000000000) (-17826384999 / 1000000000000), orderedInterval (-30923553194 / 1000000000000) (-30923553193 / 1000000000000)))) (orderedInterval (953589263 / 1000000000000) (953589899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (844410440918499 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54122778345 / 1000000000000) (-54122778340 / 1000000000000), orderedInterval (-9167274907 / 1000000000000) (-9167274902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3432481562067779 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25855168289 / 1000000000000) (-25855168206 / 1000000000000), orderedInterval (-8551565879 / 1000000000000) (-8551565796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2292738608317261 / 4000000000000) 0 (IntervalRat.scale (923 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26945127020 / 1000000000000) (26945162274 / 1000000000000), orderedInterval (-19635517786 / 1000000000000) (-19635482533 / 1000000000000)))) (orderedInterval (-3277240504 / 1000000000000) (-3277233755 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks0 :
    compactCertificate590.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate590.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate590_chunkChecks0_0
    compactCertificate590_chunkChecks0_1 compactCertificate590_chunkChecks0_2

theorem compactCertificate590_chunkChecks1_0 :
    compactCertificate590.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (923 / 2) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-16854013117 / 1000000000000) (-16854013116 / 1000000000000), orderedInterval (-33078575378 / 1000000000000) (-33078575377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1359755244912623 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42858081239 / 1000000000000) (42858081264 / 1000000000000), orderedInterval (5931213721 / 1000000000000) (5931213746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (439716908270159 / 800000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20666368947 / 1000000000000) (-20666368946 / 1000000000000), orderedInterval (-27020745671 / 1000000000000) (-27020745670 / 1000000000000)))) (orderedInterval (-14958937661 / 1000000000000) (-14958937624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (396773189187661 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-42114182373 / 1000000000000) (-42114173861 / 1000000000000), orderedInterval (68362138665 / 1000000000000) (68362147176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1065788596923817 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9553010117 / 1000000000000) (-9553010116 / 1000000000000), orderedInterval (-47919896380 / 1000000000000) (-47919896379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2893823366056389 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29504131843 / 1000000000000) (29504138051 / 1000000000000), orderedInterval (-3098749964 / 1000000000000) (-3098743756 / 1000000000000)))) (orderedInterval (-824240665 / 1000000000000) (-824239890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2131577193848557 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13181892007 / 1000000000000) (-13181891917 / 1000000000000), orderedInterval (31963637154 / 1000000000000) (31963637243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3652493853228961 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7670164125 / 1000000000000) (7670164127 / 1000000000000), orderedInterval (-25269943970 / 1000000000000) (-25269943969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2690410440918499 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27234431908 / 1000000000000) (27234431910 / 1000000000000), orderedInterval (14290158162 / 1000000000000) (14290158164 / 1000000000000)))) (orderedInterval (2045516082 / 1000000000000) (2045516128 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks1_1 :
    compactCertificate590.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4127781486464077 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18714644690 / 1000000000000) (18714646008 / 1000000000000), orderedInterval (-16339234239 / 1000000000000) (-16339232921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2383175752365733 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10390484519 / 1000000000000) (-10390484499 / 1000000000000), orderedInterval (31001647190 / 1000000000000) (31001647210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4228987193312297 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15518255642 / 1000000000000) (15518255774 / 1000000000000), orderedInterval (-19016085494 / 1000000000000) (-19016085363 / 1000000000000)))) (orderedInterval (3264461280 / 1000000000000) (3264462227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3951268405782893 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21352515784 / 1000000000000) (21352523975 / 1000000000000), orderedInterval (-13741840991 / 1000000000000) (-13741832801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2819811577628669 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27051968676 / 1000000000000) (27052062112 / 1000000000000), orderedInterval (-13105690480 / 1000000000000) (-13105597044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3197365790771451 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23428684899 / 1000000000000) (23428702148 / 1000000000000), orderedInterval (-15747640990 / 1000000000000) (-15747623740 / 1000000000000)))) (orderedInterval (-1224041334 / 1000000000000) (-1224027280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2665630254204619 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28520008642 / 1000000000000) (28520008649 / 1000000000000), orderedInterval (11891194123 / 1000000000000) (11891194130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2355165170044999 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28406508004 / 1000000000000) (-28406428026 / 1000000000000), orderedInterval (16586206154 / 1000000000000) (16586286132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (682618663250901 / 800000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11994468742 / 1000000000000) (-11994468721 / 1000000000000), orderedInterval (24547282310 / 1000000000000) (24547282331 / 1000000000000)))) (orderedInterval (149358521 / 1000000000000) (149364426 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks1_2 :
    compactCertificate590.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1888159146804047 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36719798751 / 1000000000000) (36719799285 / 1000000000000), orderedInterval (-598022886 / 1000000000000) (-598022352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1600613419535767 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36961162566 / 1000000000000) (-36961142708 / 1000000000000), orderedInterval (15039897750 / 1000000000000) (15039917608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1001589559081501 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7291840067 / 1000000000000) (-7291840048 / 1000000000000), orderedInterval (49907161719 / 1000000000000) (49907161738 / 1000000000000)))) (orderedInterval (241241608 / 1000000000000) (241242778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (538658196010467 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-24255454707 / 1000000000000) (-24255454706 / 1000000000000), orderedInterval (-64246139703 / 1000000000000) (-64246139702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1462561786112401 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37928733385 / 1000000000000) (37928758984 / 1000000000000), orderedInterval (-17444918726 / 1000000000000) (-17444893126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1997003080683377 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17826385000 / 1000000000000) (-17826384999 / 1000000000000), orderedInterval (-30923553194 / 1000000000000) (-30923553193 / 1000000000000)))) (orderedInterval (3223534460 / 1000000000000) (3223534970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (844410440918499 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54122778345 / 1000000000000) (-54122778340 / 1000000000000), orderedInterval (-9167274907 / 1000000000000) (-9167274902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3432481562067779 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25855168289 / 1000000000000) (-25855168206 / 1000000000000), orderedInterval (-8551565879 / 1000000000000) (-8551565796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2292738608317261 / 4000000000000) 1 (IntervalRat.scale (923 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26945127020 / 1000000000000) (26945162274 / 1000000000000), orderedInterval (-19635517786 / 1000000000000) (-19635482533 / 1000000000000)))) (orderedInterval (5844795654 / 1000000000000) (5844804061 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks1 :
    compactCertificate590.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate590.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate590_chunkChecks1_0
    compactCertificate590_chunkChecks1_1 compactCertificate590_chunkChecks1_2

theorem compactCertificate590_chunkChecks2_0 :
    compactCertificate590.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (923 / 2) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-16854013117 / 1000000000000) (-16854013116 / 1000000000000), orderedInterval (-33078575378 / 1000000000000) (-33078575377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1359755244912623 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42858081239 / 1000000000000) (42858081264 / 1000000000000), orderedInterval (5931213721 / 1000000000000) (5931213746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (439716908270159 / 800000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20666368947 / 1000000000000) (-20666368946 / 1000000000000), orderedInterval (-27020745671 / 1000000000000) (-27020745670 / 1000000000000)))) (orderedInterval (8216302388 / 1000000000000) (8216302430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (396773189187661 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-42114182373 / 1000000000000) (-42114173861 / 1000000000000), orderedInterval (68362138665 / 1000000000000) (68362147176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1065788596923817 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9553010117 / 1000000000000) (-9553010116 / 1000000000000), orderedInterval (-47919896380 / 1000000000000) (-47919896379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2893823366056389 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29504131843 / 1000000000000) (29504138051 / 1000000000000), orderedInterval (-3098749964 / 1000000000000) (-3098743756 / 1000000000000)))) (orderedInterval (5251244806 / 1000000000000) (5251245984 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2131577193848557 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13181892007 / 1000000000000) (-13181891917 / 1000000000000), orderedInterval (31963637154 / 1000000000000) (31963637243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3652493853228961 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7670164125 / 1000000000000) (7670164127 / 1000000000000), orderedInterval (-25269943970 / 1000000000000) (-25269943969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2690410440918499 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27234431908 / 1000000000000) (27234431910 / 1000000000000), orderedInterval (14290158162 / 1000000000000) (14290158164 / 1000000000000)))) (orderedInterval (-476345630 / 1000000000000) (-476345549 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks2_1 :
    compactCertificate590.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4127781486464077 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18714644690 / 1000000000000) (18714646008 / 1000000000000), orderedInterval (-16339234239 / 1000000000000) (-16339232921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2383175752365733 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10390484519 / 1000000000000) (-10390484499 / 1000000000000), orderedInterval (31001647190 / 1000000000000) (31001647210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4228987193312297 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15518255642 / 1000000000000) (15518255774 / 1000000000000), orderedInterval (-19016085494 / 1000000000000) (-19016085363 / 1000000000000)))) (orderedInterval (6325278293 / 1000000000000) (6325280379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3951268405782893 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21352515784 / 1000000000000) (21352523975 / 1000000000000), orderedInterval (-13741840991 / 1000000000000) (-13741832801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2819811577628669 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27051968676 / 1000000000000) (27052062112 / 1000000000000), orderedInterval (-13105690480 / 1000000000000) (-13105597044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3197365790771451 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23428684899 / 1000000000000) (23428702148 / 1000000000000), orderedInterval (-15747640990 / 1000000000000) (-15747623740 / 1000000000000)))) (orderedInterval (-3844528574 / 1000000000000) (-3844506840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2665630254204619 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28520008642 / 1000000000000) (28520008649 / 1000000000000), orderedInterval (11891194123 / 1000000000000) (11891194130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2355165170044999 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28406508004 / 1000000000000) (-28406428026 / 1000000000000), orderedInterval (16586206154 / 1000000000000) (16586286132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (682618663250901 / 800000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11994468742 / 1000000000000) (-11994468721 / 1000000000000), orderedInterval (24547282310 / 1000000000000) (24547282331 / 1000000000000)))) (orderedInterval (-2283246043 / 1000000000000) (-2283238483 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks2_2 :
    compactCertificate590.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1888159146804047 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36719798751 / 1000000000000) (36719799285 / 1000000000000), orderedInterval (-598022886 / 1000000000000) (-598022352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1600613419535767 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36961162566 / 1000000000000) (-36961142708 / 1000000000000), orderedInterval (15039897750 / 1000000000000) (15039917608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1001589559081501 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7291840067 / 1000000000000) (-7291840048 / 1000000000000), orderedInterval (49907161719 / 1000000000000) (49907161738 / 1000000000000)))) (orderedInterval (4639024559 / 1000000000000) (4639025598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (538658196010467 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-24255454707 / 1000000000000) (-24255454706 / 1000000000000), orderedInterval (-64246139703 / 1000000000000) (-64246139702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1462561786112401 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37928733385 / 1000000000000) (37928758984 / 1000000000000), orderedInterval (-17444918726 / 1000000000000) (-17444893126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1997003080683377 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17826385000 / 1000000000000) (-17826384999 / 1000000000000), orderedInterval (-30923553194 / 1000000000000) (-30923553193 / 1000000000000)))) (orderedInterval (-1103823493 / 1000000000000) (-1103823078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (844410440918499 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54122778345 / 1000000000000) (-54122778340 / 1000000000000), orderedInterval (-9167274907 / 1000000000000) (-9167274902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3432481562067779 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25855168289 / 1000000000000) (-25855168206 / 1000000000000), orderedInterval (-8551565879 / 1000000000000) (-8551565796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2292738608317261 / 4000000000000) 2 (IntervalRat.scale (923 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26945127020 / 1000000000000) (26945162274 / 1000000000000), orderedInterval (-19635517786 / 1000000000000) (-19635482533 / 1000000000000)))) (orderedInterval (577569995 / 1000000000000) (577580505 / 1000000000000))) = true
  rfl'

theorem compactCertificate590_chunkChecks2 :
    compactCertificate590.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate590.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate590_chunkChecks2_0
    compactCertificate590_chunkChecks2_1 compactCertificate590_chunkChecks2_2

theorem compactCertificate590_chunkChecks3_0 :
    compactCertificate590.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (923 / 2) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-16854013117 / 1000000000000) (-16854013116 / 1000000000000), orderedInterval (-33078575378 / 1000000000000) (-33078575377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1359755244912623 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42858081239 / 1000000000000) (42858081264 / 1000000000000), orderedInterval (5931213721 / 1000000000000) (5931213746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (439716908270159 / 800000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20666368947 / 1000000000000) (-20666368946 / 1000000000000), orderedInterval (-27020745671 / 1000000000000) (-27020745670 / 1000000000000)))) (orderedInterval (15749965905 / 1000000000000) (15749965954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (396773189187661 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-42114182373 / 1000000000000) (-42114173861 / 1000000000000), orderedInterval (68362138665 / 1000000000000) (68362147176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1065788596923817 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9553010117 / 1000000000000) (-9553010116 / 1000000000000), orderedInterval (-47919896380 / 1000000000000) (-47919896379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2893823366056389 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29504131843 / 1000000000000) (29504138051 / 1000000000000), orderedInterval (-3098749964 / 1000000000000) (-3098743756 / 1000000000000)))) (orderedInterval (-515920883 / 1000000000000) (-515919049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2131577193848557 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13181892007 / 1000000000000) (-13181891917 / 1000000000000), orderedInterval (31963637154 / 1000000000000) (31963637243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3652493853228961 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7670164125 / 1000000000000) (7670164127 / 1000000000000), orderedInterval (-25269943970 / 1000000000000) (-25269943969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2690410440918499 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27234431908 / 1000000000000) (27234431910 / 1000000000000), orderedInterval (14290158162 / 1000000000000) (14290158164 / 1000000000000)))) (orderedInterval (-7105486750 / 1000000000000) (-7105486604 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate590_chunkChecks3_1 :
    compactCertificate590.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4127781486464077 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18714644690 / 1000000000000) (18714646008 / 1000000000000), orderedInterval (-16339234239 / 1000000000000) (-16339232921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2383175752365733 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10390484519 / 1000000000000) (-10390484499 / 1000000000000), orderedInterval (31001647190 / 1000000000000) (31001647210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4228987193312297 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15518255642 / 1000000000000) (15518255774 / 1000000000000), orderedInterval (-19016085494 / 1000000000000) (-19016085363 / 1000000000000)))) (orderedInterval (-4914441146 / 1000000000000) (-4914436517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3951268405782893 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21352515784 / 1000000000000) (21352523975 / 1000000000000), orderedInterval (-13741840991 / 1000000000000) (-13741832801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2819811577628669 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27051968676 / 1000000000000) (27052062112 / 1000000000000), orderedInterval (-13105690480 / 1000000000000) (-13105597044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3197365790771451 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23428684899 / 1000000000000) (23428702148 / 1000000000000), orderedInterval (-15747640990 / 1000000000000) (-15747623740 / 1000000000000)))) (orderedInterval (1578561834 / 1000000000000) (1578595526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2665630254204619 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28520008642 / 1000000000000) (28520008649 / 1000000000000), orderedInterval (11891194123 / 1000000000000) (11891194130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2355165170044999 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28406508004 / 1000000000000) (-28406428026 / 1000000000000), orderedInterval (16586206154 / 1000000000000) (16586286132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (682618663250901 / 800000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11994468742 / 1000000000000) (-11994468721 / 1000000000000), orderedInterval (24547282310 / 1000000000000) (24547282331 / 1000000000000)))) (orderedInterval (-2409838651 / 1000000000000) (-2409828980 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate590_chunkChecks3_2 :
    compactCertificate590.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1888159146804047 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36719798751 / 1000000000000) (36719799285 / 1000000000000), orderedInterval (-598022886 / 1000000000000) (-598022352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1600613419535767 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36961162566 / 1000000000000) (-36961142708 / 1000000000000), orderedInterval (15039897750 / 1000000000000) (15039917608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1001589559081501 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7291840067 / 1000000000000) (-7291840048 / 1000000000000), orderedInterval (49907161719 / 1000000000000) (49907161738 / 1000000000000)))) (orderedInterval (183028469 / 1000000000000) (183029394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (538658196010467 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-24255454707 / 1000000000000) (-24255454706 / 1000000000000), orderedInterval (-64246139703 / 1000000000000) (-64246139702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1462561786112401 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37928733385 / 1000000000000) (37928758984 / 1000000000000), orderedInterval (-17444918726 / 1000000000000) (-17444893126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1997003080683377 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17826385000 / 1000000000000) (-17826384999 / 1000000000000), orderedInterval (-30923553194 / 1000000000000) (-30923553193 / 1000000000000)))) (orderedInterval (-3224300284 / 1000000000000) (-3224299943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (844410440918499 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54122778345 / 1000000000000) (-54122778340 / 1000000000000), orderedInterval (-9167274907 / 1000000000000) (-9167274902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3432481562067779 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25855168289 / 1000000000000) (-25855168206 / 1000000000000), orderedInterval (-8551565879 / 1000000000000) (-8551565796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2292738608317261 / 4000000000000) 3 (IntervalRat.scale (923 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26945127020 / 1000000000000) (26945162274 / 1000000000000), orderedInterval (-19635517786 / 1000000000000) (-19635482533 / 1000000000000)))) (orderedInterval (-11529481929 / 1000000000000) (-11529468782 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate590_chunkChecks3 :
    compactCertificate590.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate590.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate590_chunkChecks3_0
    compactCertificate590_chunkChecks3_1 compactCertificate590_chunkChecks3_2

theorem compactCertificate590_chunkChecks4_0 :
    compactCertificate590.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (923 / 2) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-16854013117 / 1000000000000) (-16854013116 / 1000000000000), orderedInterval (-33078575378 / 1000000000000) (-33078575377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1359755244912623 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42858081239 / 1000000000000) (42858081264 / 1000000000000), orderedInterval (5931213721 / 1000000000000) (5931213746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (439716908270159 / 800000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20666368947 / 1000000000000) (-20666368946 / 1000000000000), orderedInterval (-27020745671 / 1000000000000) (-27020745670 / 1000000000000)))) (orderedInterval (-9071099173 / 1000000000000) (-9071099115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (396773189187661 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-42114182373 / 1000000000000) (-42114173861 / 1000000000000), orderedInterval (68362138665 / 1000000000000) (68362147176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1065788596923817 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9553010117 / 1000000000000) (-9553010116 / 1000000000000), orderedInterval (-47919896380 / 1000000000000) (-47919896379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2893823366056389 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29504131843 / 1000000000000) (29504138051 / 1000000000000), orderedInterval (-3098749964 / 1000000000000) (-3098743756 / 1000000000000)))) (orderedInterval (-12701842189 / 1000000000000) (-12701839315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2131577193848557 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13181892007 / 1000000000000) (-13181891917 / 1000000000000), orderedInterval (31963637154 / 1000000000000) (31963637243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3652493853228961 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7670164125 / 1000000000000) (7670164127 / 1000000000000), orderedInterval (-25269943970 / 1000000000000) (-25269943969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2690410440918499 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27234431908 / 1000000000000) (27234431910 / 1000000000000), orderedInterval (14290158162 / 1000000000000) (14290158164 / 1000000000000)))) (orderedInterval (-625370902 / 1000000000000) (-625370631 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate590_chunkChecks4_1 :
    compactCertificate590.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4127781486464077 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18714644690 / 1000000000000) (18714646008 / 1000000000000), orderedInterval (-16339234239 / 1000000000000) (-16339232921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2383175752365733 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10390484519 / 1000000000000) (-10390484499 / 1000000000000), orderedInterval (31001647190 / 1000000000000) (31001647210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4228987193312297 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15518255642 / 1000000000000) (15518255774 / 1000000000000), orderedInterval (-19016085494 / 1000000000000) (-19016085363 / 1000000000000)))) (orderedInterval (-24490094621 / 1000000000000) (-24490084280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3951268405782893 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21352515784 / 1000000000000) (21352523975 / 1000000000000), orderedInterval (-13741840991 / 1000000000000) (-13741832801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2819811577628669 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (27051968676 / 1000000000000) (27052062112 / 1000000000000), orderedInterval (-13105690480 / 1000000000000) (-13105597044 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3197365790771451 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23428684899 / 1000000000000) (23428702148 / 1000000000000), orderedInterval (-15747640990 / 1000000000000) (-15747623740 / 1000000000000)))) (orderedInterval (4762241229 / 1000000000000) (4762293802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2665630254204619 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28520008642 / 1000000000000) (28520008649 / 1000000000000), orderedInterval (11891194123 / 1000000000000) (11891194130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2355165170044999 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28406508004 / 1000000000000) (-28406428026 / 1000000000000), orderedInterval (16586206154 / 1000000000000) (16586286132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (682618663250901 / 800000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11994468742 / 1000000000000) (-11994468721 / 1000000000000), orderedInterval (24547282310 / 1000000000000) (24547282331 / 1000000000000)))) (orderedInterval (2160498286 / 1000000000000) (2160510693 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate590_chunkChecks4_2 :
    compactCertificate590.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1888159146804047 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36719798751 / 1000000000000) (36719799285 / 1000000000000), orderedInterval (-598022886 / 1000000000000) (-598022352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1600613419535767 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36961162566 / 1000000000000) (-36961142708 / 1000000000000), orderedInterval (15039897750 / 1000000000000) (15039917608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1001589559081501 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7291840067 / 1000000000000) (-7291840048 / 1000000000000), orderedInterval (49907161719 / 1000000000000) (49907161738 / 1000000000000)))) (orderedInterval (-5265123958 / 1000000000000) (-5265123128 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (538658196010467 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-24255454707 / 1000000000000) (-24255454706 / 1000000000000), orderedInterval (-64246139703 / 1000000000000) (-64246139702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1462561786112401 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37928733385 / 1000000000000) (37928758984 / 1000000000000), orderedInterval (-17444918726 / 1000000000000) (-17444893126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1997003080683377 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17826385000 / 1000000000000) (-17826384999 / 1000000000000), orderedInterval (-30923553194 / 1000000000000) (-30923553193 / 1000000000000)))) (orderedInterval (1549272781 / 1000000000000) (1549273065 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (844410440918499 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54122778345 / 1000000000000) (-54122778340 / 1000000000000), orderedInterval (-9167274907 / 1000000000000) (-9167274902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3432481562067779 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25855168289 / 1000000000000) (-25855168206 / 1000000000000), orderedInterval (-8551565879 / 1000000000000) (-8551565796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2292738608317261 / 4000000000000) 4 (IntervalRat.scale (923 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26945127020 / 1000000000000) (26945162274 / 1000000000000), orderedInterval (-19635517786 / 1000000000000) (-19635482533 / 1000000000000)))) (orderedInterval (13164309847 / 1000000000000) (13164326379 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate590_chunkChecks4 :
    compactCertificate590.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate590.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate590_chunkChecks4_0
    compactCertificate590_chunkChecks4_1 compactCertificate590_chunkChecks4_2

theorem compactCertificate590_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate590.chunkCheck r b = true :=
  compactCertificate590.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate590_chunkChecks0
    · exact compactCertificate590_chunkChecks1
    · exact compactCertificate590_chunkChecks2
    · exact compactCertificate590_chunkChecks3
    · exact compactCertificate590_chunkChecks4)

theorem compactCertificate590_coefficient0 :
    compactCertificate590.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate590_coefficient1 :
    compactCertificate590.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate590_coefficient2 :
    compactCertificate590.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate590_coefficient3 :
    compactCertificate590.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate590_coefficient4 :
    compactCertificate590.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate590_coefficients : ∀ r : Fin 5,
    compactCertificate590.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate590_coefficient0
  · exact compactCertificate590_coefficient1
  · exact compactCertificate590_coefficient2
  · exact compactCertificate590_coefficient3
  · exact compactCertificate590_coefficient4

theorem compactCertificate590_lower : (1 : ℚ) ≤ compactCertificate590.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate590, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate590_proves {t : ℝ} (ht : t ∈ compactCertificate590.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate590.proves compactCertificate590_states compactCertificate590_chunks
    compactCertificate590_coefficients compactCertificate590_lower ht

end Erdos232
