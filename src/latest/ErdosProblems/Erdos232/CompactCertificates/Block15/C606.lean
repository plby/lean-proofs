/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate606 : CompactCertificate where
  left := 477
  right := 478
  center := 955 / 2
  grid := fun i =>
    match i.val with
    | 0 => 152
    | 1 => 112
    | 2 => 181
    | 3 => 33
    | 4 => 88
    | 5 => 238
    | 6 => 176
    | 7 => 301
    | 8 => 222
    | 9 => 340
    | 10 => 196
    | 11 => 348
    | 12 => 325
    | 13 => 232
    | 14 => 263
    | 15 => 220
    | 16 => 194
    | 17 => 281
    | 18 => 156
    | 19 => 132
    | 20 => 83
    | 21 => 44
    | 22 => 120
    | 23 => 165
    | 24 => 70
    | 25 => 283
    | _ => 189
  point := fun i =>
    match i.val with
    | 0 => 955 / 2
    | 1 => 281379471049091 / 800000000000
    | 2 => 90992339631203 / 160000000000
    | 3 => 82105827881737 / 800000000000
    | 4 => 220547802830389 / 800000000000
    | 5 => 598830187342113 / 800000000000
    | 6 => 441095605660969 / 800000000000
    | 7 => 755824838533837 / 800000000000
    | 8 => 556737155162983 / 800000000000
    | 9 => 854177967404809 / 800000000000
    | 10 => 493159879416961 / 800000000000
    | 11 => 875120860154549 / 800000000000
    | 12 => 817651425248681 / 800000000000
    | 13 => 583514638490873 / 800000000000
    | 14 => 661643408491167 / 800000000000
    | 15 => 551609294207023 / 800000000000
    | 16 => 487363540063483 / 800000000000
    | 17 => 141256949816817 / 160000000000
    | 18 => 390724157139299 / 800000000000
    | 19 => 331221195158539 / 800000000000
    | 20 => 207262844837017 / 800000000000
    | 21 => 111466647278439 / 800000000000
    | 22 => 302653630712317 / 800000000000
    | 23 => 413247658082909 / 800000000000
    | 24 => 174737155162983 / 800000000000
    | 25 => 710296834620743 / 800000000000
    | _ => 474445367484937 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (25235606262 / 1000000000000) (25235606263 / 1000000000000), orderedInterval (26362954510 / 1000000000000) (26362954511 / 1000000000000))
    | 1 => (orderedInterval (25781072933 / 1000000000000) (25781072934 / 1000000000000), orderedInterval (33806121137 / 1000000000000) (33806121138 / 1000000000000))
    | 2 => (orderedInterval (-25334585386 / 1000000000000) (-25334585385 / 1000000000000), orderedInterval (-21831430949 / 1000000000000) (-21831430948 / 1000000000000))
    | 3 => (orderedInterval (19949624618 / 1000000000000) (19949624892 / 1000000000000), orderedInterval (-76287710978 / 1000000000000) (-76287710704 / 1000000000000))
    | 4 => (orderedInterval (458661514 / 1000000000000) (458661516 / 1000000000000), orderedInterval (48051477166 / 1000000000000) (48051477168 / 1000000000000))
    | 5 => (orderedInterval (29121931123 / 1000000000000) (29121935282 / 1000000000000), orderedInterval (-1567794757 / 1000000000000) (-1567790598 / 1000000000000))
    | 6 => (orderedInterval (-23547553340 / 1000000000000) (-23547546122 / 1000000000000), orderedInterval (24518868318 / 1000000000000) (24518875537 / 1000000000000))
    | 7 => (orderedInterval (1377076677 / 1000000000000) (1377076678 / 1000000000000), orderedInterval (-25922372113 / 1000000000000) (-25922372112 / 1000000000000))
    | 8 => (orderedInterval (-20099950196 / 1000000000000) (-20099948019 / 1000000000000), orderedInterval (22614858350 / 1000000000000) (22614860527 / 1000000000000))
    | 9 => (orderedInterval (8744237454 / 1000000000000) (8744237455 / 1000000000000), orderedInterval (22794572566 / 1000000000000) (22794572567 / 1000000000000))
    | 10 => (orderedInterval (32011846671 / 1000000000000) (32011847037 / 1000000000000), orderedInterval (2795526545 / 1000000000000) (2795526911 / 1000000000000))
    | 11 => (orderedInterval (23821012392 / 1000000000000) (23821015188 / 1000000000000), orderedInterval (3801094331 / 1000000000000) (3801097127 / 1000000000000))
    | 12 => (orderedInterval (-24111336310 / 1000000000000) (-24111228453 / 1000000000000), orderedInterval (6455527759 / 1000000000000) (6455635616 / 1000000000000))
    | 13 => (orderedInterval (28684083179 / 1000000000000) (28684083278 / 1000000000000), orderedInterval (7053558066 / 1000000000000) (7053558166 / 1000000000000))
    | 14 => (orderedInterval (-27731900387 / 1000000000000) (-27731895431 / 1000000000000), orderedInterval (844623504 / 1000000000000) (844628460 / 1000000000000))
    | 15 => (orderedInterval (-22899214354 / 1000000000000) (-22899205697 / 1000000000000), orderedInterval (19989507611 / 1000000000000) (19989516268 / 1000000000000))
    | 16 => (orderedInterval (16080429981 / 1000000000000) (16080429982 / 1000000000000), orderedInterval (28030015806 / 1000000000000) (28030015807 / 1000000000000))
    | 17 => (orderedInterval (-20238920697 / 1000000000000) (-20238920696 / 1000000000000), orderedInterval (-17637260597 / 1000000000000) (-17637260596 / 1000000000000))
    | 18 => (orderedInterval (-28238545766 / 1000000000000) (-28238510686 / 1000000000000), orderedInterval (22524485259 / 1000000000000) (22524520339 / 1000000000000))
    | 19 => (orderedInterval (4747167430 / 1000000000000) (4747167431 / 1000000000000), orderedInterval (38918501277 / 1000000000000) (38918501278 / 1000000000000))
    | 20 => (orderedInterval (38479829594 / 1000000000000) (38479918682 / 1000000000000), orderedInterval (-31324014979 / 1000000000000) (-31323925892 / 1000000000000))
    | 21 => (orderedInterval (64227892541 / 1000000000000) (64227895107 / 1000000000000), orderedInterval (-21296951417 / 1000000000000) (-21296948850 / 1000000000000))
    | 22 => (orderedInterval (35180453391 / 1000000000000) (35180525787 / 1000000000000), orderedInterval (-21143931324 / 1000000000000) (-21143858929 / 1000000000000))
    | 23 => (orderedInterval (29878231108 / 1000000000000) (29878319434 / 1000000000000), orderedInterval (-18460216774 / 1000000000000) (-18460128447 / 1000000000000))
    | 24 => (orderedInterval (-34994503755 / 1000000000000) (-34994482896 / 1000000000000), orderedInterval (41190024117 / 1000000000000) (41190044976 / 1000000000000))
    | 25 => (orderedInterval (10782088760 / 1000000000000) (10782088769 / 1000000000000), orderedInterval (-24516578265 / 1000000000000) (-24516578257 / 1000000000000))
    | _ => (orderedInterval (-2647203808 / 1000000000000) (-2647203807 / 1000000000000), orderedInterval (-32654280960 / 1000000000000) (-32654280959 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8756078115 / 1000000000000) (8756078149 / 1000000000000)
      | 1 => orderedInterval (-2269960706 / 1000000000000) (-2269960350 / 1000000000000)
      | 2 => orderedInterval (-528250707 / 1000000000000) (-528250627 / 1000000000000)
      | 3 => orderedInterval (4204366165 / 1000000000000) (4204366779 / 1000000000000)
      | 4 => orderedInterval (3288070531 / 1000000000000) (3288072569 / 1000000000000)
      | 5 => orderedInterval (-1702858480 / 1000000000000) (-1702858334 / 1000000000000)
      | 6 => orderedInterval (5499156185 / 1000000000000) (5499164814 / 1000000000000)
      | 7 => orderedInterval (-4273951999 / 1000000000000) (-4273943483 / 1000000000000)
      | _ => orderedInterval (-591953942 / 1000000000000) (-591953683 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9155604279 / 1000000000000) (9155604317 / 1000000000000)
      | 1 => orderedInterval (1365541264 / 1000000000000) (1365541793 / 1000000000000)
      | 2 => orderedInterval (2378554469 / 1000000000000) (2378554593 / 1000000000000)
      | 3 => orderedInterval (-7551514911 / 1000000000000) (-7551513573 / 1000000000000)
      | 4 => orderedInterval (762006325 / 1000000000000) (762010643 / 1000000000000)
      | 5 => orderedInterval (-2548115191 / 1000000000000) (-2548114980 / 1000000000000)
      | 6 => orderedInterval (-6147018996 / 1000000000000) (-6147011574 / 1000000000000)
      | 7 => orderedInterval (2025291189 / 1000000000000) (2025299879 / 1000000000000)
      | _ => orderedInterval (11433924525 / 1000000000000) (11433924770 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-8043227521 / 1000000000000) (-8043227477 / 1000000000000)
      | 1 => orderedInterval (5089088813 / 1000000000000) (5089089631 / 1000000000000)
      | 2 => orderedInterval (1193134342 / 1000000000000) (1193134537 / 1000000000000)
      | 3 => orderedInterval (-13940407939 / 1000000000000) (-13940404964 / 1000000000000)
      | 4 => orderedInterval (-8745924897 / 1000000000000) (-8745915717 / 1000000000000)
      | 5 => orderedInterval (3826034708 / 1000000000000) (3826035015 / 1000000000000)
      | 6 => orderedInterval (-4877625372 / 1000000000000) (-4877618529 / 1000000000000)
      | 7 => orderedInterval (3277516275 / 1000000000000) (3277525301 / 1000000000000)
      | _ => orderedInterval (2288540166 / 1000000000000) (2288540470 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8394073985 / 1000000000000) (-8394073934 / 1000000000000)
      | 1 => orderedInterval (-785868015 / 1000000000000) (-785866740 / 1000000000000)
      | 2 => orderedInterval (-7887723236 / 1000000000000) (-7887722922 / 1000000000000)
      | 3 => orderedInterval (38370829403 / 1000000000000) (38370836089 / 1000000000000)
      | 4 => orderedInterval (-1193953709 / 1000000000000) (-1193934172 / 1000000000000)
      | 5 => orderedInterval (5482294793 / 1000000000000) (5482295246 / 1000000000000)
      | 6 => orderedInterval (5462937231 / 1000000000000) (5462943813 / 1000000000000)
      | 7 => orderedInterval (-2046320641 / 1000000000000) (-2046311182 / 1000000000000)
      | _ => orderedInterval (-24596647248 / 1000000000000) (-24596646808 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (7117065947 / 1000000000000) (7117066006 / 1000000000000)
      | 1 => orderedInterval (-12497527735 / 1000000000000) (-12497525737 / 1000000000000)
      | 2 => orderedInterval (-2809638244 / 1000000000000) (-2809637727 / 1000000000000)
      | 3 => orderedInterval (60854345022 / 1000000000000) (60854360160 / 1000000000000)
      | 4 => orderedInterval (25172511056 / 1000000000000) (25172552734 / 1000000000000)
      | 5 => orderedInterval (-9666415190 / 1000000000000) (-9666414513 / 1000000000000)
      | 6 => orderedInterval (4875730588 / 1000000000000) (4875737107 / 1000000000000)
      | 7 => orderedInterval (-3450628175 / 1000000000000) (-3450618162 / 1000000000000)
      | _ => orderedInterval (-9215952121 / 1000000000000) (-9215951428 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (12380695162 / 1000000000000) (12380715834 / 1000000000000)
    | 1 => orderedInterval (10874272953 / 1000000000000) (10874295868 / 1000000000000)
    | 2 => orderedInterval (-19932871425 / 1000000000000) (-19932841733 / 1000000000000)
    | 3 => orderedInterval (4411474593 / 1000000000000) (4411519390 / 1000000000000)
    | _ => orderedInterval (60379491148 / 1000000000000) (60379568440 / 1000000000000)

theorem compactCertificate606_stateChecks0 :
    compactCertificate606.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (955 / 2)) (orderedInterval (25235606262 / 1000000000000) (25235606263 / 1000000000000), orderedInterval (26362954510 / 1000000000000) (26362954511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (281379471049091 / 800000000000)) (orderedInterval (25781072933 / 1000000000000) (25781072934 / 1000000000000), orderedInterval (33806121137 / 1000000000000) (33806121138 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (90992339631203 / 160000000000)) (orderedInterval (-25334585386 / 1000000000000) (-25334585385 / 1000000000000), orderedInterval (-21831430949 / 1000000000000) (-21831430948 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_stateChecks1 :
    compactCertificate606.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (82105827881737 / 800000000000)) (orderedInterval (19949624618 / 1000000000000) (19949624892 / 1000000000000), orderedInterval (-76287710978 / 1000000000000) (-76287710704 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (220547802830389 / 800000000000)) (orderedInterval (458661514 / 1000000000000) (458661516 / 1000000000000), orderedInterval (48051477166 / 1000000000000) (48051477168 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (598830187342113 / 800000000000)) (orderedInterval (29121931123 / 1000000000000) (29121935282 / 1000000000000), orderedInterval (-1567794757 / 1000000000000) (-1567790598 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_stateChecks2 :
    compactCertificate606.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (441095605660969 / 800000000000)) (orderedInterval (-23547553340 / 1000000000000) (-23547546122 / 1000000000000), orderedInterval (24518868318 / 1000000000000) (24518875537 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 301 12 (755824838533837 / 800000000000)) (orderedInterval (1377076677 / 1000000000000) (1377076678 / 1000000000000), orderedInterval (-25922372113 / 1000000000000) (-25922372112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (556737155162983 / 800000000000)) (orderedInterval (-20099950196 / 1000000000000) (-20099948019 / 1000000000000), orderedInterval (22614858350 / 1000000000000) (22614860527 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_stateChecks3 :
    compactCertificate606.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 340 12 (854177967404809 / 800000000000)) (orderedInterval (8744237454 / 1000000000000) (8744237455 / 1000000000000), orderedInterval (22794572566 / 1000000000000) (22794572567 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (493159879416961 / 800000000000)) (orderedInterval (32011846671 / 1000000000000) (32011847037 / 1000000000000), orderedInterval (2795526545 / 1000000000000) (2795526911 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 348 12 (875120860154549 / 800000000000)) (orderedInterval (23821012392 / 1000000000000) (23821015188 / 1000000000000), orderedInterval (3801094331 / 1000000000000) (3801097127 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_stateChecks4 :
    compactCertificate606.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 325 12 (817651425248681 / 800000000000)) (orderedInterval (-24111336310 / 1000000000000) (-24111228453 / 1000000000000), orderedInterval (6455527759 / 1000000000000) (6455635616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (583514638490873 / 800000000000)) (orderedInterval (28684083179 / 1000000000000) (28684083278 / 1000000000000), orderedInterval (7053558066 / 1000000000000) (7053558166 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (661643408491167 / 800000000000)) (orderedInterval (-27731900387 / 1000000000000) (-27731895431 / 1000000000000), orderedInterval (844623504 / 1000000000000) (844628460 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_stateChecks5 :
    compactCertificate606.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (551609294207023 / 800000000000)) (orderedInterval (-22899214354 / 1000000000000) (-22899205697 / 1000000000000), orderedInterval (19989507611 / 1000000000000) (19989516268 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (487363540063483 / 800000000000)) (orderedInterval (16080429981 / 1000000000000) (16080429982 / 1000000000000), orderedInterval (28030015806 / 1000000000000) (28030015807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (141256949816817 / 160000000000)) (orderedInterval (-20238920697 / 1000000000000) (-20238920696 / 1000000000000), orderedInterval (-17637260597 / 1000000000000) (-17637260596 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_stateChecks6 :
    compactCertificate606.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (390724157139299 / 800000000000)) (orderedInterval (-28238545766 / 1000000000000) (-28238510686 / 1000000000000), orderedInterval (22524485259 / 1000000000000) (22524520339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (331221195158539 / 800000000000)) (orderedInterval (4747167430 / 1000000000000) (4747167431 / 1000000000000), orderedInterval (38918501277 / 1000000000000) (38918501278 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (207262844837017 / 800000000000)) (orderedInterval (38479829594 / 1000000000000) (38479918682 / 1000000000000), orderedInterval (-31324014979 / 1000000000000) (-31323925892 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_stateChecks7 :
    compactCertificate606.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (111466647278439 / 800000000000)) (orderedInterval (64227892541 / 1000000000000) (64227895107 / 1000000000000), orderedInterval (-21296951417 / 1000000000000) (-21296948850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (302653630712317 / 800000000000)) (orderedInterval (35180453391 / 1000000000000) (35180525787 / 1000000000000), orderedInterval (-21143931324 / 1000000000000) (-21143858929 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (413247658082909 / 800000000000)) (orderedInterval (29878231108 / 1000000000000) (29878319434 / 1000000000000), orderedInterval (-18460216774 / 1000000000000) (-18460128447 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_stateChecks8 :
    compactCertificate606.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (174737155162983 / 800000000000)) (orderedInterval (-34994503755 / 1000000000000) (-34994482896 / 1000000000000), orderedInterval (41190024117 / 1000000000000) (41190044976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (710296834620743 / 800000000000)) (orderedInterval (10782088760 / 1000000000000) (10782088769 / 1000000000000), orderedInterval (-24516578265 / 1000000000000) (-24516578257 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (474445367484937 / 800000000000)) (orderedInterval (-2647203808 / 1000000000000) (-2647203807 / 1000000000000), orderedInterval (-32654280960 / 1000000000000) (-32654280959 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_states : ∀ j,
    BesselStateValid (compactCertificate606.point j) (compactCertificate606.state j) :=
  compactCertificate606.statesValid_of_checks3 compactCertificate606_stateChecks0
    compactCertificate606_stateChecks1 compactCertificate606_stateChecks2
    compactCertificate606_stateChecks3 compactCertificate606_stateChecks4
    compactCertificate606_stateChecks5 compactCertificate606_stateChecks6
    compactCertificate606_stateChecks7 compactCertificate606_stateChecks8

theorem compactCertificate606_chunkChecks0_0 :
    compactCertificate606.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (955 / 2) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25235606262 / 1000000000000) (25235606263 / 1000000000000), orderedInterval (26362954510 / 1000000000000) (26362954511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (281379471049091 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25781072933 / 1000000000000) (25781072934 / 1000000000000), orderedInterval (33806121137 / 1000000000000) (33806121138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (90992339631203 / 160000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25334585386 / 1000000000000) (-25334585385 / 1000000000000), orderedInterval (-21831430949 / 1000000000000) (-21831430948 / 1000000000000)))) (orderedInterval (8756078115 / 1000000000000) (8756078149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (82105827881737 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19949624618 / 1000000000000) (19949624892 / 1000000000000), orderedInterval (-76287710978 / 1000000000000) (-76287710704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (220547802830389 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (458661514 / 1000000000000) (458661516 / 1000000000000), orderedInterval (48051477166 / 1000000000000) (48051477168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (598830187342113 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29121931123 / 1000000000000) (29121935282 / 1000000000000), orderedInterval (-1567794757 / 1000000000000) (-1567790598 / 1000000000000)))) (orderedInterval (-2269960706 / 1000000000000) (-2269960350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (441095605660969 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23547553340 / 1000000000000) (-23547546122 / 1000000000000), orderedInterval (24518868318 / 1000000000000) (24518875537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (755824838533837 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1377076677 / 1000000000000) (1377076678 / 1000000000000), orderedInterval (-25922372113 / 1000000000000) (-25922372112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (556737155162983 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20099950196 / 1000000000000) (-20099948019 / 1000000000000), orderedInterval (22614858350 / 1000000000000) (22614860527 / 1000000000000)))) (orderedInterval (-528250707 / 1000000000000) (-528250627 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks0_1 :
    compactCertificate606.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (854177967404809 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8744237454 / 1000000000000) (8744237455 / 1000000000000), orderedInterval (22794572566 / 1000000000000) (22794572567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (493159879416961 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32011846671 / 1000000000000) (32011847037 / 1000000000000), orderedInterval (2795526545 / 1000000000000) (2795526911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (875120860154549 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23821012392 / 1000000000000) (23821015188 / 1000000000000), orderedInterval (3801094331 / 1000000000000) (3801097127 / 1000000000000)))) (orderedInterval (4204366165 / 1000000000000) (4204366779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (817651425248681 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24111336310 / 1000000000000) (-24111228453 / 1000000000000), orderedInterval (6455527759 / 1000000000000) (6455635616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (583514638490873 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28684083179 / 1000000000000) (28684083278 / 1000000000000), orderedInterval (7053558066 / 1000000000000) (7053558166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (661643408491167 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27731900387 / 1000000000000) (-27731895431 / 1000000000000), orderedInterval (844623504 / 1000000000000) (844628460 / 1000000000000)))) (orderedInterval (3288070531 / 1000000000000) (3288072569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (551609294207023 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22899214354 / 1000000000000) (-22899205697 / 1000000000000), orderedInterval (19989507611 / 1000000000000) (19989516268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (487363540063483 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16080429981 / 1000000000000) (16080429982 / 1000000000000), orderedInterval (28030015806 / 1000000000000) (28030015807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (141256949816817 / 160000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20238920697 / 1000000000000) (-20238920696 / 1000000000000), orderedInterval (-17637260597 / 1000000000000) (-17637260596 / 1000000000000)))) (orderedInterval (-1702858480 / 1000000000000) (-1702858334 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks0_2 :
    compactCertificate606.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (390724157139299 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28238545766 / 1000000000000) (-28238510686 / 1000000000000), orderedInterval (22524485259 / 1000000000000) (22524520339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (331221195158539 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4747167430 / 1000000000000) (4747167431 / 1000000000000), orderedInterval (38918501277 / 1000000000000) (38918501278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (207262844837017 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38479829594 / 1000000000000) (38479918682 / 1000000000000), orderedInterval (-31324014979 / 1000000000000) (-31323925892 / 1000000000000)))) (orderedInterval (5499156185 / 1000000000000) (5499164814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (111466647278439 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64227892541 / 1000000000000) (64227895107 / 1000000000000), orderedInterval (-21296951417 / 1000000000000) (-21296948850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (302653630712317 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35180453391 / 1000000000000) (35180525787 / 1000000000000), orderedInterval (-21143931324 / 1000000000000) (-21143858929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (413247658082909 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29878231108 / 1000000000000) (29878319434 / 1000000000000), orderedInterval (-18460216774 / 1000000000000) (-18460128447 / 1000000000000)))) (orderedInterval (-4273951999 / 1000000000000) (-4273943483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (174737155162983 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34994503755 / 1000000000000) (-34994482896 / 1000000000000), orderedInterval (41190024117 / 1000000000000) (41190044976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (710296834620743 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10782088760 / 1000000000000) (10782088769 / 1000000000000), orderedInterval (-24516578265 / 1000000000000) (-24516578257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (474445367484937 / 800000000000) 0 (IntervalRat.scale (955 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2647203808 / 1000000000000) (-2647203807 / 1000000000000), orderedInterval (-32654280960 / 1000000000000) (-32654280959 / 1000000000000)))) (orderedInterval (-591953942 / 1000000000000) (-591953683 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks0 :
    compactCertificate606.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate606.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate606_chunkChecks0_0
    compactCertificate606_chunkChecks0_1 compactCertificate606_chunkChecks0_2

theorem compactCertificate606_chunkChecks1_0 :
    compactCertificate606.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (955 / 2) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25235606262 / 1000000000000) (25235606263 / 1000000000000), orderedInterval (26362954510 / 1000000000000) (26362954511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (281379471049091 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25781072933 / 1000000000000) (25781072934 / 1000000000000), orderedInterval (33806121137 / 1000000000000) (33806121138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (90992339631203 / 160000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25334585386 / 1000000000000) (-25334585385 / 1000000000000), orderedInterval (-21831430949 / 1000000000000) (-21831430948 / 1000000000000)))) (orderedInterval (9155604279 / 1000000000000) (9155604317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (82105827881737 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19949624618 / 1000000000000) (19949624892 / 1000000000000), orderedInterval (-76287710978 / 1000000000000) (-76287710704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (220547802830389 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (458661514 / 1000000000000) (458661516 / 1000000000000), orderedInterval (48051477166 / 1000000000000) (48051477168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (598830187342113 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29121931123 / 1000000000000) (29121935282 / 1000000000000), orderedInterval (-1567794757 / 1000000000000) (-1567790598 / 1000000000000)))) (orderedInterval (1365541264 / 1000000000000) (1365541793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (441095605660969 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23547553340 / 1000000000000) (-23547546122 / 1000000000000), orderedInterval (24518868318 / 1000000000000) (24518875537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (755824838533837 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1377076677 / 1000000000000) (1377076678 / 1000000000000), orderedInterval (-25922372113 / 1000000000000) (-25922372112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (556737155162983 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20099950196 / 1000000000000) (-20099948019 / 1000000000000), orderedInterval (22614858350 / 1000000000000) (22614860527 / 1000000000000)))) (orderedInterval (2378554469 / 1000000000000) (2378554593 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks1_1 :
    compactCertificate606.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (854177967404809 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8744237454 / 1000000000000) (8744237455 / 1000000000000), orderedInterval (22794572566 / 1000000000000) (22794572567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (493159879416961 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32011846671 / 1000000000000) (32011847037 / 1000000000000), orderedInterval (2795526545 / 1000000000000) (2795526911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (875120860154549 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23821012392 / 1000000000000) (23821015188 / 1000000000000), orderedInterval (3801094331 / 1000000000000) (3801097127 / 1000000000000)))) (orderedInterval (-7551514911 / 1000000000000) (-7551513573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (817651425248681 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24111336310 / 1000000000000) (-24111228453 / 1000000000000), orderedInterval (6455527759 / 1000000000000) (6455635616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (583514638490873 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28684083179 / 1000000000000) (28684083278 / 1000000000000), orderedInterval (7053558066 / 1000000000000) (7053558166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (661643408491167 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27731900387 / 1000000000000) (-27731895431 / 1000000000000), orderedInterval (844623504 / 1000000000000) (844628460 / 1000000000000)))) (orderedInterval (762006325 / 1000000000000) (762010643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (551609294207023 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22899214354 / 1000000000000) (-22899205697 / 1000000000000), orderedInterval (19989507611 / 1000000000000) (19989516268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (487363540063483 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16080429981 / 1000000000000) (16080429982 / 1000000000000), orderedInterval (28030015806 / 1000000000000) (28030015807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (141256949816817 / 160000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20238920697 / 1000000000000) (-20238920696 / 1000000000000), orderedInterval (-17637260597 / 1000000000000) (-17637260596 / 1000000000000)))) (orderedInterval (-2548115191 / 1000000000000) (-2548114980 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks1_2 :
    compactCertificate606.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (390724157139299 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28238545766 / 1000000000000) (-28238510686 / 1000000000000), orderedInterval (22524485259 / 1000000000000) (22524520339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (331221195158539 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4747167430 / 1000000000000) (4747167431 / 1000000000000), orderedInterval (38918501277 / 1000000000000) (38918501278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (207262844837017 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38479829594 / 1000000000000) (38479918682 / 1000000000000), orderedInterval (-31324014979 / 1000000000000) (-31323925892 / 1000000000000)))) (orderedInterval (-6147018996 / 1000000000000) (-6147011574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (111466647278439 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64227892541 / 1000000000000) (64227895107 / 1000000000000), orderedInterval (-21296951417 / 1000000000000) (-21296948850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (302653630712317 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35180453391 / 1000000000000) (35180525787 / 1000000000000), orderedInterval (-21143931324 / 1000000000000) (-21143858929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (413247658082909 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29878231108 / 1000000000000) (29878319434 / 1000000000000), orderedInterval (-18460216774 / 1000000000000) (-18460128447 / 1000000000000)))) (orderedInterval (2025291189 / 1000000000000) (2025299879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (174737155162983 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34994503755 / 1000000000000) (-34994482896 / 1000000000000), orderedInterval (41190024117 / 1000000000000) (41190044976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (710296834620743 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10782088760 / 1000000000000) (10782088769 / 1000000000000), orderedInterval (-24516578265 / 1000000000000) (-24516578257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (474445367484937 / 800000000000) 1 (IntervalRat.scale (955 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2647203808 / 1000000000000) (-2647203807 / 1000000000000), orderedInterval (-32654280960 / 1000000000000) (-32654280959 / 1000000000000)))) (orderedInterval (11433924525 / 1000000000000) (11433924770 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks1 :
    compactCertificate606.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate606.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate606_chunkChecks1_0
    compactCertificate606_chunkChecks1_1 compactCertificate606_chunkChecks1_2

theorem compactCertificate606_chunkChecks2_0 :
    compactCertificate606.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (955 / 2) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25235606262 / 1000000000000) (25235606263 / 1000000000000), orderedInterval (26362954510 / 1000000000000) (26362954511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (281379471049091 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25781072933 / 1000000000000) (25781072934 / 1000000000000), orderedInterval (33806121137 / 1000000000000) (33806121138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (90992339631203 / 160000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25334585386 / 1000000000000) (-25334585385 / 1000000000000), orderedInterval (-21831430949 / 1000000000000) (-21831430948 / 1000000000000)))) (orderedInterval (-8043227521 / 1000000000000) (-8043227477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (82105827881737 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19949624618 / 1000000000000) (19949624892 / 1000000000000), orderedInterval (-76287710978 / 1000000000000) (-76287710704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (220547802830389 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (458661514 / 1000000000000) (458661516 / 1000000000000), orderedInterval (48051477166 / 1000000000000) (48051477168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (598830187342113 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29121931123 / 1000000000000) (29121935282 / 1000000000000), orderedInterval (-1567794757 / 1000000000000) (-1567790598 / 1000000000000)))) (orderedInterval (5089088813 / 1000000000000) (5089089631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (441095605660969 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23547553340 / 1000000000000) (-23547546122 / 1000000000000), orderedInterval (24518868318 / 1000000000000) (24518875537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (755824838533837 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1377076677 / 1000000000000) (1377076678 / 1000000000000), orderedInterval (-25922372113 / 1000000000000) (-25922372112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (556737155162983 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20099950196 / 1000000000000) (-20099948019 / 1000000000000), orderedInterval (22614858350 / 1000000000000) (22614860527 / 1000000000000)))) (orderedInterval (1193134342 / 1000000000000) (1193134537 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks2_1 :
    compactCertificate606.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (854177967404809 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8744237454 / 1000000000000) (8744237455 / 1000000000000), orderedInterval (22794572566 / 1000000000000) (22794572567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (493159879416961 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32011846671 / 1000000000000) (32011847037 / 1000000000000), orderedInterval (2795526545 / 1000000000000) (2795526911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (875120860154549 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23821012392 / 1000000000000) (23821015188 / 1000000000000), orderedInterval (3801094331 / 1000000000000) (3801097127 / 1000000000000)))) (orderedInterval (-13940407939 / 1000000000000) (-13940404964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (817651425248681 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24111336310 / 1000000000000) (-24111228453 / 1000000000000), orderedInterval (6455527759 / 1000000000000) (6455635616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (583514638490873 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28684083179 / 1000000000000) (28684083278 / 1000000000000), orderedInterval (7053558066 / 1000000000000) (7053558166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (661643408491167 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27731900387 / 1000000000000) (-27731895431 / 1000000000000), orderedInterval (844623504 / 1000000000000) (844628460 / 1000000000000)))) (orderedInterval (-8745924897 / 1000000000000) (-8745915717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (551609294207023 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22899214354 / 1000000000000) (-22899205697 / 1000000000000), orderedInterval (19989507611 / 1000000000000) (19989516268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (487363540063483 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16080429981 / 1000000000000) (16080429982 / 1000000000000), orderedInterval (28030015806 / 1000000000000) (28030015807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (141256949816817 / 160000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20238920697 / 1000000000000) (-20238920696 / 1000000000000), orderedInterval (-17637260597 / 1000000000000) (-17637260596 / 1000000000000)))) (orderedInterval (3826034708 / 1000000000000) (3826035015 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks2_2 :
    compactCertificate606.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (390724157139299 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28238545766 / 1000000000000) (-28238510686 / 1000000000000), orderedInterval (22524485259 / 1000000000000) (22524520339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (331221195158539 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4747167430 / 1000000000000) (4747167431 / 1000000000000), orderedInterval (38918501277 / 1000000000000) (38918501278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (207262844837017 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38479829594 / 1000000000000) (38479918682 / 1000000000000), orderedInterval (-31324014979 / 1000000000000) (-31323925892 / 1000000000000)))) (orderedInterval (-4877625372 / 1000000000000) (-4877618529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (111466647278439 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64227892541 / 1000000000000) (64227895107 / 1000000000000), orderedInterval (-21296951417 / 1000000000000) (-21296948850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (302653630712317 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35180453391 / 1000000000000) (35180525787 / 1000000000000), orderedInterval (-21143931324 / 1000000000000) (-21143858929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (413247658082909 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29878231108 / 1000000000000) (29878319434 / 1000000000000), orderedInterval (-18460216774 / 1000000000000) (-18460128447 / 1000000000000)))) (orderedInterval (3277516275 / 1000000000000) (3277525301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (174737155162983 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34994503755 / 1000000000000) (-34994482896 / 1000000000000), orderedInterval (41190024117 / 1000000000000) (41190044976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (710296834620743 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10782088760 / 1000000000000) (10782088769 / 1000000000000), orderedInterval (-24516578265 / 1000000000000) (-24516578257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (474445367484937 / 800000000000) 2 (IntervalRat.scale (955 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2647203808 / 1000000000000) (-2647203807 / 1000000000000), orderedInterval (-32654280960 / 1000000000000) (-32654280959 / 1000000000000)))) (orderedInterval (2288540166 / 1000000000000) (2288540470 / 1000000000000))) = true
  rfl'

theorem compactCertificate606_chunkChecks2 :
    compactCertificate606.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate606.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate606_chunkChecks2_0
    compactCertificate606_chunkChecks2_1 compactCertificate606_chunkChecks2_2

theorem compactCertificate606_chunkChecks3_0 :
    compactCertificate606.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (955 / 2) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25235606262 / 1000000000000) (25235606263 / 1000000000000), orderedInterval (26362954510 / 1000000000000) (26362954511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (281379471049091 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25781072933 / 1000000000000) (25781072934 / 1000000000000), orderedInterval (33806121137 / 1000000000000) (33806121138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (90992339631203 / 160000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25334585386 / 1000000000000) (-25334585385 / 1000000000000), orderedInterval (-21831430949 / 1000000000000) (-21831430948 / 1000000000000)))) (orderedInterval (-8394073985 / 1000000000000) (-8394073934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (82105827881737 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19949624618 / 1000000000000) (19949624892 / 1000000000000), orderedInterval (-76287710978 / 1000000000000) (-76287710704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (220547802830389 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (458661514 / 1000000000000) (458661516 / 1000000000000), orderedInterval (48051477166 / 1000000000000) (48051477168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (598830187342113 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29121931123 / 1000000000000) (29121935282 / 1000000000000), orderedInterval (-1567794757 / 1000000000000) (-1567790598 / 1000000000000)))) (orderedInterval (-785868015 / 1000000000000) (-785866740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (441095605660969 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23547553340 / 1000000000000) (-23547546122 / 1000000000000), orderedInterval (24518868318 / 1000000000000) (24518875537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (755824838533837 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1377076677 / 1000000000000) (1377076678 / 1000000000000), orderedInterval (-25922372113 / 1000000000000) (-25922372112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (556737155162983 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20099950196 / 1000000000000) (-20099948019 / 1000000000000), orderedInterval (22614858350 / 1000000000000) (22614860527 / 1000000000000)))) (orderedInterval (-7887723236 / 1000000000000) (-7887722922 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate606_chunkChecks3_1 :
    compactCertificate606.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (854177967404809 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8744237454 / 1000000000000) (8744237455 / 1000000000000), orderedInterval (22794572566 / 1000000000000) (22794572567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (493159879416961 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32011846671 / 1000000000000) (32011847037 / 1000000000000), orderedInterval (2795526545 / 1000000000000) (2795526911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (875120860154549 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23821012392 / 1000000000000) (23821015188 / 1000000000000), orderedInterval (3801094331 / 1000000000000) (3801097127 / 1000000000000)))) (orderedInterval (38370829403 / 1000000000000) (38370836089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (817651425248681 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24111336310 / 1000000000000) (-24111228453 / 1000000000000), orderedInterval (6455527759 / 1000000000000) (6455635616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (583514638490873 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28684083179 / 1000000000000) (28684083278 / 1000000000000), orderedInterval (7053558066 / 1000000000000) (7053558166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (661643408491167 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27731900387 / 1000000000000) (-27731895431 / 1000000000000), orderedInterval (844623504 / 1000000000000) (844628460 / 1000000000000)))) (orderedInterval (-1193953709 / 1000000000000) (-1193934172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (551609294207023 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22899214354 / 1000000000000) (-22899205697 / 1000000000000), orderedInterval (19989507611 / 1000000000000) (19989516268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (487363540063483 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16080429981 / 1000000000000) (16080429982 / 1000000000000), orderedInterval (28030015806 / 1000000000000) (28030015807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (141256949816817 / 160000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20238920697 / 1000000000000) (-20238920696 / 1000000000000), orderedInterval (-17637260597 / 1000000000000) (-17637260596 / 1000000000000)))) (orderedInterval (5482294793 / 1000000000000) (5482295246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate606_chunkChecks3_2 :
    compactCertificate606.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (390724157139299 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28238545766 / 1000000000000) (-28238510686 / 1000000000000), orderedInterval (22524485259 / 1000000000000) (22524520339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (331221195158539 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4747167430 / 1000000000000) (4747167431 / 1000000000000), orderedInterval (38918501277 / 1000000000000) (38918501278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (207262844837017 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38479829594 / 1000000000000) (38479918682 / 1000000000000), orderedInterval (-31324014979 / 1000000000000) (-31323925892 / 1000000000000)))) (orderedInterval (5462937231 / 1000000000000) (5462943813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (111466647278439 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64227892541 / 1000000000000) (64227895107 / 1000000000000), orderedInterval (-21296951417 / 1000000000000) (-21296948850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (302653630712317 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35180453391 / 1000000000000) (35180525787 / 1000000000000), orderedInterval (-21143931324 / 1000000000000) (-21143858929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (413247658082909 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29878231108 / 1000000000000) (29878319434 / 1000000000000), orderedInterval (-18460216774 / 1000000000000) (-18460128447 / 1000000000000)))) (orderedInterval (-2046320641 / 1000000000000) (-2046311182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (174737155162983 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34994503755 / 1000000000000) (-34994482896 / 1000000000000), orderedInterval (41190024117 / 1000000000000) (41190044976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (710296834620743 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10782088760 / 1000000000000) (10782088769 / 1000000000000), orderedInterval (-24516578265 / 1000000000000) (-24516578257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (474445367484937 / 800000000000) 3 (IntervalRat.scale (955 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2647203808 / 1000000000000) (-2647203807 / 1000000000000), orderedInterval (-32654280960 / 1000000000000) (-32654280959 / 1000000000000)))) (orderedInterval (-24596647248 / 1000000000000) (-24596646808 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate606_chunkChecks3 :
    compactCertificate606.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate606.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate606_chunkChecks3_0
    compactCertificate606_chunkChecks3_1 compactCertificate606_chunkChecks3_2

theorem compactCertificate606_chunkChecks4_0 :
    compactCertificate606.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (955 / 2) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25235606262 / 1000000000000) (25235606263 / 1000000000000), orderedInterval (26362954510 / 1000000000000) (26362954511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (281379471049091 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25781072933 / 1000000000000) (25781072934 / 1000000000000), orderedInterval (33806121137 / 1000000000000) (33806121138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (90992339631203 / 160000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25334585386 / 1000000000000) (-25334585385 / 1000000000000), orderedInterval (-21831430949 / 1000000000000) (-21831430948 / 1000000000000)))) (orderedInterval (7117065947 / 1000000000000) (7117066006 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (82105827881737 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19949624618 / 1000000000000) (19949624892 / 1000000000000), orderedInterval (-76287710978 / 1000000000000) (-76287710704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (220547802830389 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (458661514 / 1000000000000) (458661516 / 1000000000000), orderedInterval (48051477166 / 1000000000000) (48051477168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (598830187342113 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29121931123 / 1000000000000) (29121935282 / 1000000000000), orderedInterval (-1567794757 / 1000000000000) (-1567790598 / 1000000000000)))) (orderedInterval (-12497527735 / 1000000000000) (-12497525737 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (441095605660969 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23547553340 / 1000000000000) (-23547546122 / 1000000000000), orderedInterval (24518868318 / 1000000000000) (24518875537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (755824838533837 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1377076677 / 1000000000000) (1377076678 / 1000000000000), orderedInterval (-25922372113 / 1000000000000) (-25922372112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (556737155162983 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20099950196 / 1000000000000) (-20099948019 / 1000000000000), orderedInterval (22614858350 / 1000000000000) (22614860527 / 1000000000000)))) (orderedInterval (-2809638244 / 1000000000000) (-2809637727 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate606_chunkChecks4_1 :
    compactCertificate606.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (854177967404809 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8744237454 / 1000000000000) (8744237455 / 1000000000000), orderedInterval (22794572566 / 1000000000000) (22794572567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (493159879416961 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32011846671 / 1000000000000) (32011847037 / 1000000000000), orderedInterval (2795526545 / 1000000000000) (2795526911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (875120860154549 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23821012392 / 1000000000000) (23821015188 / 1000000000000), orderedInterval (3801094331 / 1000000000000) (3801097127 / 1000000000000)))) (orderedInterval (60854345022 / 1000000000000) (60854360160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (817651425248681 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24111336310 / 1000000000000) (-24111228453 / 1000000000000), orderedInterval (6455527759 / 1000000000000) (6455635616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (583514638490873 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28684083179 / 1000000000000) (28684083278 / 1000000000000), orderedInterval (7053558066 / 1000000000000) (7053558166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (661643408491167 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27731900387 / 1000000000000) (-27731895431 / 1000000000000), orderedInterval (844623504 / 1000000000000) (844628460 / 1000000000000)))) (orderedInterval (25172511056 / 1000000000000) (25172552734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (551609294207023 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22899214354 / 1000000000000) (-22899205697 / 1000000000000), orderedInterval (19989507611 / 1000000000000) (19989516268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (487363540063483 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16080429981 / 1000000000000) (16080429982 / 1000000000000), orderedInterval (28030015806 / 1000000000000) (28030015807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (141256949816817 / 160000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20238920697 / 1000000000000) (-20238920696 / 1000000000000), orderedInterval (-17637260597 / 1000000000000) (-17637260596 / 1000000000000)))) (orderedInterval (-9666415190 / 1000000000000) (-9666414513 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate606_chunkChecks4_2 :
    compactCertificate606.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (390724157139299 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28238545766 / 1000000000000) (-28238510686 / 1000000000000), orderedInterval (22524485259 / 1000000000000) (22524520339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (331221195158539 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4747167430 / 1000000000000) (4747167431 / 1000000000000), orderedInterval (38918501277 / 1000000000000) (38918501278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (207262844837017 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38479829594 / 1000000000000) (38479918682 / 1000000000000), orderedInterval (-31324014979 / 1000000000000) (-31323925892 / 1000000000000)))) (orderedInterval (4875730588 / 1000000000000) (4875737107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (111466647278439 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64227892541 / 1000000000000) (64227895107 / 1000000000000), orderedInterval (-21296951417 / 1000000000000) (-21296948850 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (302653630712317 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (35180453391 / 1000000000000) (35180525787 / 1000000000000), orderedInterval (-21143931324 / 1000000000000) (-21143858929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (413247658082909 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (29878231108 / 1000000000000) (29878319434 / 1000000000000), orderedInterval (-18460216774 / 1000000000000) (-18460128447 / 1000000000000)))) (orderedInterval (-3450628175 / 1000000000000) (-3450618162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (174737155162983 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34994503755 / 1000000000000) (-34994482896 / 1000000000000), orderedInterval (41190024117 / 1000000000000) (41190044976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (710296834620743 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10782088760 / 1000000000000) (10782088769 / 1000000000000), orderedInterval (-24516578265 / 1000000000000) (-24516578257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (474445367484937 / 800000000000) 4 (IntervalRat.scale (955 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2647203808 / 1000000000000) (-2647203807 / 1000000000000), orderedInterval (-32654280960 / 1000000000000) (-32654280959 / 1000000000000)))) (orderedInterval (-9215952121 / 1000000000000) (-9215951428 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate606_chunkChecks4 :
    compactCertificate606.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate606.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate606_chunkChecks4_0
    compactCertificate606_chunkChecks4_1 compactCertificate606_chunkChecks4_2

theorem compactCertificate606_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate606.chunkCheck r b = true :=
  compactCertificate606.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate606_chunkChecks0
    · exact compactCertificate606_chunkChecks1
    · exact compactCertificate606_chunkChecks2
    · exact compactCertificate606_chunkChecks3
    · exact compactCertificate606_chunkChecks4)

theorem compactCertificate606_coefficient0 :
    compactCertificate606.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate606_coefficient1 :
    compactCertificate606.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate606_coefficient2 :
    compactCertificate606.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate606_coefficient3 :
    compactCertificate606.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate606_coefficient4 :
    compactCertificate606.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate606_coefficients : ∀ r : Fin 5,
    compactCertificate606.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate606_coefficient0
  · exact compactCertificate606_coefficient1
  · exact compactCertificate606_coefficient2
  · exact compactCertificate606_coefficient3
  · exact compactCertificate606_coefficient4

theorem compactCertificate606_lower : (1 : ℚ) ≤ compactCertificate606.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate606, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate606_proves {t : ℝ} (ht : t ∈ compactCertificate606.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate606.proves compactCertificate606_states compactCertificate606_chunks
    compactCertificate606_coefficients compactCertificate606_lower ht

end Erdos232
