/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate419 : CompactCertificate where
  left := 290
  right := 291
  center := 581 / 2
  grid := fun i =>
    match i.val with
    | 0 => 93
    | 1 => 68
    | 2 => 110
    | 3 => 20
    | 4 => 53
    | 5 => 145
    | 6 => 107
    | 7 => 183
    | 8 => 135
    | 9 => 207
    | 10 => 119
    | 11 => 212
    | 12 => 198
    | 13 => 141
    | 14 => 160
    | 15 => 134
    | 16 => 118
    | 17 => 171
    | 18 => 95
    | 19 => 80
    | 20 => 50
    | 21 => 27
    | 22 => 73
    | 23 => 100
    | 24 => 42
    | 25 => 172
    | _ => 115
  point := fun i =>
    match i.val with
    | 0 => 581 / 2
    | 1 => 855923940730481 / 4000000000000
    | 2 => 276788216365073 / 800000000000
    | 3 => 249756471200467 / 4000000000000
    | 4 => 670881012798199 / 4000000000000
    | 5 => 1821572454689883 / 4000000000000
    | 6 => 1341762025596979 / 4000000000000
    | 7 => 2299132100461567 / 4000000000000
    | 8 => 1693530299213053 / 4000000000000
    | 9 => 2598310989854419 / 4000000000000
    | 10 => 1500135549430651 / 4000000000000
    | 11 => 2662016857328759 / 4000000000000
    | 12 => 2487201455861171 / 4000000000000
    | 13 => 1774984319179043 / 4000000000000
    | 14 => 2012643038394597 / 4000000000000
    | 15 => 1677931936828693 / 4000000000000
    | 16 => 1482503752758553 / 4000000000000
    | 17 => 429687370908747 / 800000000000
    | 18 => 1188537881141009 / 4000000000000
    | 19 => 1007536724539849 / 4000000000000
    | 20 => 630469700786947 / 4000000000000
    | 21 => 339068701930749 / 4000000000000
    | 22 => 920637483999247 / 4000000000000
    | 23 => 1257051776681519 / 4000000000000
    | 24 => 531530299213053 / 4000000000000
    | 25 => 2160641156621213 / 4000000000000
    | _ => 1443208159731667 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (36174320395 / 1000000000000) (36174394650 / 1000000000000), orderedInterval (-29775550069 / 1000000000000) (-29775475814 / 1000000000000))
    | 1 => (orderedInterval (49503936443 / 1000000000000) (49503936444 / 1000000000000), orderedInterval (22785814242 / 1000000000000) (22785814243 / 1000000000000))
    | 2 => (orderedInterval (39903817967 / 1000000000000) (39903817969 / 1000000000000), orderedInterval (15680941053 / 1000000000000) (15680941054 / 1000000000000))
    | 3 => (orderedInterval (38450459768 / 1000000000000) (38450459769 / 1000000000000), orderedInterval (93060432138 / 1000000000000) (93060432139 / 1000000000000))
    | 4 => (orderedInterval (-56008481920 / 1000000000000) (-56008472167 / 1000000000000), orderedInterval (25833349103 / 1000000000000) (25833358856 / 1000000000000))
    | 5 => (orderedInterval (-22547092167 / 1000000000000) (-22547092166 / 1000000000000), orderedInterval (-29801162394 / 1000000000000) (-29801162393 / 1000000000000))
    | 6 => (orderedInterval (-3269395744 / 1000000000000) (-3269395743 / 1000000000000), orderedInterval (-43436755175 / 1000000000000) (-43436755174 / 1000000000000))
    | 7 => (orderedInterval (-20319200558 / 1000000000000) (-20319200557 / 1000000000000), orderedInterval (-26339732552 / 1000000000000) (-26339732551 / 1000000000000))
    | 8 => (orderedInterval (-2041417033 / 1000000000000) (-2041417032 / 1000000000000), orderedInterval (-38720773313 / 1000000000000) (-38720773312 / 1000000000000))
    | 9 => (orderedInterval (-1666991872 / 1000000000000) (-1666991871 / 1000000000000), orderedInterval (-31260084746 / 1000000000000) (-31260084745 / 1000000000000))
    | 10 => (orderedInterval (-37970312178 / 1000000000000) (-37970292219 / 1000000000000), orderedInterval (16042935408 / 1000000000000) (16042955367 / 1000000000000))
    | 11 => (orderedInterval (8302820832 / 1000000000000) (8302820833 / 1000000000000), orderedInterval (29787403188 / 1000000000000) (29787403189 / 1000000000000))
    | 12 => (orderedInterval (16730508505 / 1000000000000) (16730508506 / 1000000000000), orderedInterval (27261504107 / 1000000000000) (27261504108 / 1000000000000))
    | 13 => (orderedInterval (-37876417534 / 1000000000000) (-37876417186 / 1000000000000), orderedInterval (-115048823 / 1000000000000) (-115048474 / 1000000000000))
    | 14 => (orderedInterval (34187788889 / 1000000000000) (34187788899 / 1000000000000), orderedInterval (9786203103 / 1000000000000) (9786203113 / 1000000000000))
    | 15 => (orderedInterval (-25255121609 / 1000000000000) (-25255113894 / 1000000000000), orderedInterval (29691668824 / 1000000000000) (29691676539 / 1000000000000))
    | 16 => (orderedInterval (26796652604 / 1000000000000) (26796652605 / 1000000000000), orderedInterval (31580740413 / 1000000000000) (31580740414 / 1000000000000))
    | 17 => (orderedInterval (-21702370806 / 1000000000000) (-21702370805 / 1000000000000), orderedInterval (-26705773767 / 1000000000000) (-26705773766 / 1000000000000))
    | 18 => (orderedInterval (23473863092 / 1000000000000) (23473865446 / 1000000000000), orderedInterval (-39933235635 / 1000000000000) (-39933233282 / 1000000000000))
    | 19 => (orderedInterval (48959628180 / 1000000000000) (48959628183 / 1000000000000), orderedInterval (11321258514 / 1000000000000) (11321258517 / 1000000000000))
    | 20 => (orderedInterval (61602503277 / 1000000000000) (61602503278 / 1000000000000), orderedInterval (15429330813 / 1000000000000) (15429330814 / 1000000000000))
    | 21 => (orderedInterval (-57668456427 / 1000000000000) (-57668456426 / 1000000000000), orderedInterval (-64348181839 / 1000000000000) (-64348181838 / 1000000000000))
    | 22 => (orderedInterval (-52556350603 / 1000000000000) (-52556350460 / 1000000000000), orderedInterval (2068388480 / 1000000000000) (2068388623 / 1000000000000))
    | 23 => (orderedInterval (34937279227 / 1000000000000) (34937279228 / 1000000000000), orderedInterval (28319422935 / 1000000000000) (28319422936 / 1000000000000))
    | 24 => (orderedInterval (68445230116 / 1000000000000) (68445230449 / 1000000000000), orderedInterval (-10556210932 / 1000000000000) (-10556210599 / 1000000000000))
    | 25 => (orderedInterval (19143410360 / 1000000000000) (19143410361 / 1000000000000), orderedInterval (28479748140 / 1000000000000) (28479748141 / 1000000000000))
    | _ => (orderedInterval (-12571323072 / 1000000000000) (-12571323071 / 1000000000000), orderedInterval (-40062754190 / 1000000000000) (-40062754189 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17141116418 / 1000000000000) (17141145871 / 1000000000000)
      | 1 => orderedInterval (-859263023 / 1000000000000) (-859262631 / 1000000000000)
      | 2 => orderedInterval (577388412 / 1000000000000) (577388429 / 1000000000000)
      | 3 => orderedInterval (-1336788503 / 1000000000000) (-1336786908 / 1000000000000)
      | 4 => orderedInterval (-4056749826 / 1000000000000) (-4056749758 / 1000000000000)
      | 5 => orderedInterval (-2380787625 / 1000000000000) (-2380787507 / 1000000000000)
      | 6 => orderedInterval (-4518920318 / 1000000000000) (-4518919869 / 1000000000000)
      | 7 => orderedInterval (-420360153 / 1000000000000) (-420360115 / 1000000000000)
      | _ => orderedInterval (1213016323 / 1000000000000) (1213016406 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10549663771 / 1000000000000) (-10549634316 / 1000000000000)
      | 1 => orderedInterval (3648643946 / 1000000000000) (3648644192 / 1000000000000)
      | 2 => orderedInterval (243591715 / 1000000000000) (243591744 / 1000000000000)
      | 3 => orderedInterval (23655548042 / 1000000000000) (23655550191 / 1000000000000)
      | 4 => orderedInterval (-1155827298 / 1000000000000) (-1155827191 / 1000000000000)
      | 5 => orderedInterval (-3074873405 / 1000000000000) (-3074873236 / 1000000000000)
      | 6 => orderedInterval (6247777372 / 1000000000000) (6247777825 / 1000000000000)
      | 7 => orderedInterval (-2038370496 / 1000000000000) (-2038370461 / 1000000000000)
      | _ => orderedInterval (4996139926 / 1000000000000) (4996140041 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17873739506 / 1000000000000) (-17873709946 / 1000000000000)
      | 1 => orderedInterval (-3250555452 / 1000000000000) (-3250555277 / 1000000000000)
      | 2 => orderedInterval (-2349580830 / 1000000000000) (-2349580779 / 1000000000000)
      | 3 => orderedInterval (-3068051043 / 1000000000000) (-3068048058 / 1000000000000)
      | 4 => orderedInterval (10264104634 / 1000000000000) (10264104805 / 1000000000000)
      | 5 => orderedInterval (5014305482 / 1000000000000) (5014305729 / 1000000000000)
      | 6 => orderedInterval (5398151520 / 1000000000000) (5398151980 / 1000000000000)
      | 7 => orderedInterval (2301414003 / 1000000000000) (2301414037 / 1000000000000)
      | _ => orderedInterval (1645714319 / 1000000000000) (1645714487 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10223952292 / 1000000000000) (10223981855 / 1000000000000)
      | 1 => orderedInterval (-8321586546 / 1000000000000) (-8321586394 / 1000000000000)
      | 2 => orderedInterval (-3387894513 / 1000000000000) (-3387894420 / 1000000000000)
      | 3 => orderedInterval (-115559357979 / 1000000000000) (-115559353664 / 1000000000000)
      | 4 => orderedInterval (5087079530 / 1000000000000) (5087079806 / 1000000000000)
      | 5 => orderedInterval (7025202911 / 1000000000000) (7025203273 / 1000000000000)
      | 6 => orderedInterval (-6513584175 / 1000000000000) (-6513583708 / 1000000000000)
      | 7 => orderedInterval (2733603417 / 1000000000000) (2733603452 / 1000000000000)
      | _ => orderedInterval (503010149 / 1000000000000) (503010408 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (19114924915 / 1000000000000) (19114954585 / 1000000000000)
      | 1 => orderedInterval (9508760300 / 1000000000000) (9508760468 / 1000000000000)
      | 2 => orderedInterval (9405945605 / 1000000000000) (9405945776 / 1000000000000)
      | 3 => orderedInterval (32895391231 / 1000000000000) (32895397858 / 1000000000000)
      | 4 => orderedInterval (-27432235194 / 1000000000000) (-27432234739 / 1000000000000)
      | 5 => orderedInterval (-11872732046 / 1000000000000) (-11872731510 / 1000000000000)
      | 6 => orderedInterval (-5455677138 / 1000000000000) (-5455676661 / 1000000000000)
      | 7 => orderedInterval (-3208384748 / 1000000000000) (-3208384712 / 1000000000000)
      | _ => orderedInterval (-13000447842 / 1000000000000) (-13000447427 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (5358651705 / 1000000000000) (5358683918 / 1000000000000)
    | 1 => orderedInterval (21972966031 / 1000000000000) (21972998789 / 1000000000000)
    | 2 => orderedInterval (-1918236873 / 1000000000000) (-1918203022 / 1000000000000)
    | 3 => orderedInterval (-108209574914 / 1000000000000) (-108209539392 / 1000000000000)
    | _ => orderedInterval (9955545083 / 1000000000000) (9955583638 / 1000000000000)

theorem compactCertificate419_stateChecks0 :
    compactCertificate419.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (581 / 2)) (orderedInterval (36174320395 / 1000000000000) (36174394650 / 1000000000000), orderedInterval (-29775550069 / 1000000000000) (-29775475814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (855923940730481 / 4000000000000)) (orderedInterval (49503936443 / 1000000000000) (49503936444 / 1000000000000), orderedInterval (22785814242 / 1000000000000) (22785814243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (276788216365073 / 800000000000)) (orderedInterval (39903817967 / 1000000000000) (39903817969 / 1000000000000), orderedInterval (15680941053 / 1000000000000) (15680941054 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_stateChecks1 :
    compactCertificate419.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (249756471200467 / 4000000000000)) (orderedInterval (38450459768 / 1000000000000) (38450459769 / 1000000000000), orderedInterval (93060432138 / 1000000000000) (93060432139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (670881012798199 / 4000000000000)) (orderedInterval (-56008481920 / 1000000000000) (-56008472167 / 1000000000000), orderedInterval (25833349103 / 1000000000000) (25833358856 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1821572454689883 / 4000000000000)) (orderedInterval (-22547092167 / 1000000000000) (-22547092166 / 1000000000000), orderedInterval (-29801162394 / 1000000000000) (-29801162393 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_stateChecks2 :
    compactCertificate419.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1341762025596979 / 4000000000000)) (orderedInterval (-3269395744 / 1000000000000) (-3269395743 / 1000000000000), orderedInterval (-43436755175 / 1000000000000) (-43436755174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2299132100461567 / 4000000000000)) (orderedInterval (-20319200558 / 1000000000000) (-20319200557 / 1000000000000), orderedInterval (-26339732552 / 1000000000000) (-26339732551 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1693530299213053 / 4000000000000)) (orderedInterval (-2041417033 / 1000000000000) (-2041417032 / 1000000000000), orderedInterval (-38720773313 / 1000000000000) (-38720773312 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_stateChecks3 :
    compactCertificate419.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2598310989854419 / 4000000000000)) (orderedInterval (-1666991872 / 1000000000000) (-1666991871 / 1000000000000), orderedInterval (-31260084746 / 1000000000000) (-31260084745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1500135549430651 / 4000000000000)) (orderedInterval (-37970312178 / 1000000000000) (-37970292219 / 1000000000000), orderedInterval (16042935408 / 1000000000000) (16042955367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2662016857328759 / 4000000000000)) (orderedInterval (8302820832 / 1000000000000) (8302820833 / 1000000000000), orderedInterval (29787403188 / 1000000000000) (29787403189 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_stateChecks4 :
    compactCertificate419.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2487201455861171 / 4000000000000)) (orderedInterval (16730508505 / 1000000000000) (16730508506 / 1000000000000), orderedInterval (27261504107 / 1000000000000) (27261504108 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1774984319179043 / 4000000000000)) (orderedInterval (-37876417534 / 1000000000000) (-37876417186 / 1000000000000), orderedInterval (-115048823 / 1000000000000) (-115048474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2012643038394597 / 4000000000000)) (orderedInterval (34187788889 / 1000000000000) (34187788899 / 1000000000000), orderedInterval (9786203103 / 1000000000000) (9786203113 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_stateChecks5 :
    compactCertificate419.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1677931936828693 / 4000000000000)) (orderedInterval (-25255121609 / 1000000000000) (-25255113894 / 1000000000000), orderedInterval (29691668824 / 1000000000000) (29691676539 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1482503752758553 / 4000000000000)) (orderedInterval (26796652604 / 1000000000000) (26796652605 / 1000000000000), orderedInterval (31580740413 / 1000000000000) (31580740414 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (429687370908747 / 800000000000)) (orderedInterval (-21702370806 / 1000000000000) (-21702370805 / 1000000000000), orderedInterval (-26705773767 / 1000000000000) (-26705773766 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_stateChecks6 :
    compactCertificate419.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1188537881141009 / 4000000000000)) (orderedInterval (23473863092 / 1000000000000) (23473865446 / 1000000000000), orderedInterval (-39933235635 / 1000000000000) (-39933233282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1007536724539849 / 4000000000000)) (orderedInterval (48959628180 / 1000000000000) (48959628183 / 1000000000000), orderedInterval (11321258514 / 1000000000000) (11321258517 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (630469700786947 / 4000000000000)) (orderedInterval (61602503277 / 1000000000000) (61602503278 / 1000000000000), orderedInterval (15429330813 / 1000000000000) (15429330814 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_stateChecks7 :
    compactCertificate419.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (339068701930749 / 4000000000000)) (orderedInterval (-57668456427 / 1000000000000) (-57668456426 / 1000000000000), orderedInterval (-64348181839 / 1000000000000) (-64348181838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (920637483999247 / 4000000000000)) (orderedInterval (-52556350603 / 1000000000000) (-52556350460 / 1000000000000), orderedInterval (2068388480 / 1000000000000) (2068388623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1257051776681519 / 4000000000000)) (orderedInterval (34937279227 / 1000000000000) (34937279228 / 1000000000000), orderedInterval (28319422935 / 1000000000000) (28319422936 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_stateChecks8 :
    compactCertificate419.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (531530299213053 / 4000000000000)) (orderedInterval (68445230116 / 1000000000000) (68445230449 / 1000000000000), orderedInterval (-10556210932 / 1000000000000) (-10556210599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2160641156621213 / 4000000000000)) (orderedInterval (19143410360 / 1000000000000) (19143410361 / 1000000000000), orderedInterval (28479748140 / 1000000000000) (28479748141 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1443208159731667 / 4000000000000)) (orderedInterval (-12571323072 / 1000000000000) (-12571323071 / 1000000000000), orderedInterval (-40062754190 / 1000000000000) (-40062754189 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_states : ∀ j,
    BesselStateValid (compactCertificate419.point j) (compactCertificate419.state j) :=
  compactCertificate419.statesValid_of_checks3 compactCertificate419_stateChecks0
    compactCertificate419_stateChecks1 compactCertificate419_stateChecks2
    compactCertificate419_stateChecks3 compactCertificate419_stateChecks4
    compactCertificate419_stateChecks5 compactCertificate419_stateChecks6
    compactCertificate419_stateChecks7 compactCertificate419_stateChecks8

theorem compactCertificate419_chunkChecks0_0 :
    compactCertificate419.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (581 / 2) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36174320395 / 1000000000000) (36174394650 / 1000000000000), orderedInterval (-29775550069 / 1000000000000) (-29775475814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (855923940730481 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49503936443 / 1000000000000) (49503936444 / 1000000000000), orderedInterval (22785814242 / 1000000000000) (22785814243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (276788216365073 / 800000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39903817967 / 1000000000000) (39903817969 / 1000000000000), orderedInterval (15680941053 / 1000000000000) (15680941054 / 1000000000000)))) (orderedInterval (17141116418 / 1000000000000) (17141145871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (249756471200467 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38450459768 / 1000000000000) (38450459769 / 1000000000000), orderedInterval (93060432138 / 1000000000000) (93060432139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (670881012798199 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-56008481920 / 1000000000000) (-56008472167 / 1000000000000), orderedInterval (25833349103 / 1000000000000) (25833358856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1821572454689883 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22547092167 / 1000000000000) (-22547092166 / 1000000000000), orderedInterval (-29801162394 / 1000000000000) (-29801162393 / 1000000000000)))) (orderedInterval (-859263023 / 1000000000000) (-859262631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1341762025596979 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3269395744 / 1000000000000) (-3269395743 / 1000000000000), orderedInterval (-43436755175 / 1000000000000) (-43436755174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2299132100461567 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20319200558 / 1000000000000) (-20319200557 / 1000000000000), orderedInterval (-26339732552 / 1000000000000) (-26339732551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1693530299213053 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2041417033 / 1000000000000) (-2041417032 / 1000000000000), orderedInterval (-38720773313 / 1000000000000) (-38720773312 / 1000000000000)))) (orderedInterval (577388412 / 1000000000000) (577388429 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks0_1 :
    compactCertificate419.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2598310989854419 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1666991872 / 1000000000000) (-1666991871 / 1000000000000), orderedInterval (-31260084746 / 1000000000000) (-31260084745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1500135549430651 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37970312178 / 1000000000000) (-37970292219 / 1000000000000), orderedInterval (16042935408 / 1000000000000) (16042955367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2662016857328759 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8302820832 / 1000000000000) (8302820833 / 1000000000000), orderedInterval (29787403188 / 1000000000000) (29787403189 / 1000000000000)))) (orderedInterval (-1336788503 / 1000000000000) (-1336786908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2487201455861171 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16730508505 / 1000000000000) (16730508506 / 1000000000000), orderedInterval (27261504107 / 1000000000000) (27261504108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1774984319179043 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37876417534 / 1000000000000) (-37876417186 / 1000000000000), orderedInterval (-115048823 / 1000000000000) (-115048474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2012643038394597 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34187788889 / 1000000000000) (34187788899 / 1000000000000), orderedInterval (9786203103 / 1000000000000) (9786203113 / 1000000000000)))) (orderedInterval (-4056749826 / 1000000000000) (-4056749758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1677931936828693 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25255121609 / 1000000000000) (-25255113894 / 1000000000000), orderedInterval (29691668824 / 1000000000000) (29691676539 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1482503752758553 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26796652604 / 1000000000000) (26796652605 / 1000000000000), orderedInterval (31580740413 / 1000000000000) (31580740414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (429687370908747 / 800000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21702370806 / 1000000000000) (-21702370805 / 1000000000000), orderedInterval (-26705773767 / 1000000000000) (-26705773766 / 1000000000000)))) (orderedInterval (-2380787625 / 1000000000000) (-2380787507 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks0_2 :
    compactCertificate419.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1188537881141009 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23473863092 / 1000000000000) (23473865446 / 1000000000000), orderedInterval (-39933235635 / 1000000000000) (-39933233282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1007536724539849 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48959628180 / 1000000000000) (48959628183 / 1000000000000), orderedInterval (11321258514 / 1000000000000) (11321258517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (630469700786947 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61602503277 / 1000000000000) (61602503278 / 1000000000000), orderedInterval (15429330813 / 1000000000000) (15429330814 / 1000000000000)))) (orderedInterval (-4518920318 / 1000000000000) (-4518919869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (339068701930749 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57668456427 / 1000000000000) (-57668456426 / 1000000000000), orderedInterval (-64348181839 / 1000000000000) (-64348181838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (920637483999247 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52556350603 / 1000000000000) (-52556350460 / 1000000000000), orderedInterval (2068388480 / 1000000000000) (2068388623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1257051776681519 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34937279227 / 1000000000000) (34937279228 / 1000000000000), orderedInterval (28319422935 / 1000000000000) (28319422936 / 1000000000000)))) (orderedInterval (-420360153 / 1000000000000) (-420360115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (531530299213053 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68445230116 / 1000000000000) (68445230449 / 1000000000000), orderedInterval (-10556210932 / 1000000000000) (-10556210599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2160641156621213 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19143410360 / 1000000000000) (19143410361 / 1000000000000), orderedInterval (28479748140 / 1000000000000) (28479748141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1443208159731667 / 4000000000000) 0 (IntervalRat.scale (581 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12571323072 / 1000000000000) (-12571323071 / 1000000000000), orderedInterval (-40062754190 / 1000000000000) (-40062754189 / 1000000000000)))) (orderedInterval (1213016323 / 1000000000000) (1213016406 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks0 :
    compactCertificate419.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate419.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate419_chunkChecks0_0
    compactCertificate419_chunkChecks0_1 compactCertificate419_chunkChecks0_2

theorem compactCertificate419_chunkChecks1_0 :
    compactCertificate419.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (581 / 2) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36174320395 / 1000000000000) (36174394650 / 1000000000000), orderedInterval (-29775550069 / 1000000000000) (-29775475814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (855923940730481 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49503936443 / 1000000000000) (49503936444 / 1000000000000), orderedInterval (22785814242 / 1000000000000) (22785814243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (276788216365073 / 800000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39903817967 / 1000000000000) (39903817969 / 1000000000000), orderedInterval (15680941053 / 1000000000000) (15680941054 / 1000000000000)))) (orderedInterval (-10549663771 / 1000000000000) (-10549634316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (249756471200467 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38450459768 / 1000000000000) (38450459769 / 1000000000000), orderedInterval (93060432138 / 1000000000000) (93060432139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (670881012798199 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-56008481920 / 1000000000000) (-56008472167 / 1000000000000), orderedInterval (25833349103 / 1000000000000) (25833358856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1821572454689883 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22547092167 / 1000000000000) (-22547092166 / 1000000000000), orderedInterval (-29801162394 / 1000000000000) (-29801162393 / 1000000000000)))) (orderedInterval (3648643946 / 1000000000000) (3648644192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1341762025596979 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3269395744 / 1000000000000) (-3269395743 / 1000000000000), orderedInterval (-43436755175 / 1000000000000) (-43436755174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2299132100461567 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20319200558 / 1000000000000) (-20319200557 / 1000000000000), orderedInterval (-26339732552 / 1000000000000) (-26339732551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1693530299213053 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2041417033 / 1000000000000) (-2041417032 / 1000000000000), orderedInterval (-38720773313 / 1000000000000) (-38720773312 / 1000000000000)))) (orderedInterval (243591715 / 1000000000000) (243591744 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks1_1 :
    compactCertificate419.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2598310989854419 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1666991872 / 1000000000000) (-1666991871 / 1000000000000), orderedInterval (-31260084746 / 1000000000000) (-31260084745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1500135549430651 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37970312178 / 1000000000000) (-37970292219 / 1000000000000), orderedInterval (16042935408 / 1000000000000) (16042955367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2662016857328759 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8302820832 / 1000000000000) (8302820833 / 1000000000000), orderedInterval (29787403188 / 1000000000000) (29787403189 / 1000000000000)))) (orderedInterval (23655548042 / 1000000000000) (23655550191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2487201455861171 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16730508505 / 1000000000000) (16730508506 / 1000000000000), orderedInterval (27261504107 / 1000000000000) (27261504108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1774984319179043 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37876417534 / 1000000000000) (-37876417186 / 1000000000000), orderedInterval (-115048823 / 1000000000000) (-115048474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2012643038394597 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34187788889 / 1000000000000) (34187788899 / 1000000000000), orderedInterval (9786203103 / 1000000000000) (9786203113 / 1000000000000)))) (orderedInterval (-1155827298 / 1000000000000) (-1155827191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1677931936828693 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25255121609 / 1000000000000) (-25255113894 / 1000000000000), orderedInterval (29691668824 / 1000000000000) (29691676539 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1482503752758553 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26796652604 / 1000000000000) (26796652605 / 1000000000000), orderedInterval (31580740413 / 1000000000000) (31580740414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (429687370908747 / 800000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21702370806 / 1000000000000) (-21702370805 / 1000000000000), orderedInterval (-26705773767 / 1000000000000) (-26705773766 / 1000000000000)))) (orderedInterval (-3074873405 / 1000000000000) (-3074873236 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks1_2 :
    compactCertificate419.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1188537881141009 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23473863092 / 1000000000000) (23473865446 / 1000000000000), orderedInterval (-39933235635 / 1000000000000) (-39933233282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1007536724539849 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48959628180 / 1000000000000) (48959628183 / 1000000000000), orderedInterval (11321258514 / 1000000000000) (11321258517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (630469700786947 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61602503277 / 1000000000000) (61602503278 / 1000000000000), orderedInterval (15429330813 / 1000000000000) (15429330814 / 1000000000000)))) (orderedInterval (6247777372 / 1000000000000) (6247777825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (339068701930749 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57668456427 / 1000000000000) (-57668456426 / 1000000000000), orderedInterval (-64348181839 / 1000000000000) (-64348181838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (920637483999247 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52556350603 / 1000000000000) (-52556350460 / 1000000000000), orderedInterval (2068388480 / 1000000000000) (2068388623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1257051776681519 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34937279227 / 1000000000000) (34937279228 / 1000000000000), orderedInterval (28319422935 / 1000000000000) (28319422936 / 1000000000000)))) (orderedInterval (-2038370496 / 1000000000000) (-2038370461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (531530299213053 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68445230116 / 1000000000000) (68445230449 / 1000000000000), orderedInterval (-10556210932 / 1000000000000) (-10556210599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2160641156621213 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19143410360 / 1000000000000) (19143410361 / 1000000000000), orderedInterval (28479748140 / 1000000000000) (28479748141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1443208159731667 / 4000000000000) 1 (IntervalRat.scale (581 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12571323072 / 1000000000000) (-12571323071 / 1000000000000), orderedInterval (-40062754190 / 1000000000000) (-40062754189 / 1000000000000)))) (orderedInterval (4996139926 / 1000000000000) (4996140041 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks1 :
    compactCertificate419.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate419.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate419_chunkChecks1_0
    compactCertificate419_chunkChecks1_1 compactCertificate419_chunkChecks1_2

theorem compactCertificate419_chunkChecks2_0 :
    compactCertificate419.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (581 / 2) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36174320395 / 1000000000000) (36174394650 / 1000000000000), orderedInterval (-29775550069 / 1000000000000) (-29775475814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (855923940730481 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49503936443 / 1000000000000) (49503936444 / 1000000000000), orderedInterval (22785814242 / 1000000000000) (22785814243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (276788216365073 / 800000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39903817967 / 1000000000000) (39903817969 / 1000000000000), orderedInterval (15680941053 / 1000000000000) (15680941054 / 1000000000000)))) (orderedInterval (-17873739506 / 1000000000000) (-17873709946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (249756471200467 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38450459768 / 1000000000000) (38450459769 / 1000000000000), orderedInterval (93060432138 / 1000000000000) (93060432139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (670881012798199 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-56008481920 / 1000000000000) (-56008472167 / 1000000000000), orderedInterval (25833349103 / 1000000000000) (25833358856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1821572454689883 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22547092167 / 1000000000000) (-22547092166 / 1000000000000), orderedInterval (-29801162394 / 1000000000000) (-29801162393 / 1000000000000)))) (orderedInterval (-3250555452 / 1000000000000) (-3250555277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1341762025596979 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3269395744 / 1000000000000) (-3269395743 / 1000000000000), orderedInterval (-43436755175 / 1000000000000) (-43436755174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2299132100461567 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20319200558 / 1000000000000) (-20319200557 / 1000000000000), orderedInterval (-26339732552 / 1000000000000) (-26339732551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1693530299213053 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2041417033 / 1000000000000) (-2041417032 / 1000000000000), orderedInterval (-38720773313 / 1000000000000) (-38720773312 / 1000000000000)))) (orderedInterval (-2349580830 / 1000000000000) (-2349580779 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks2_1 :
    compactCertificate419.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2598310989854419 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1666991872 / 1000000000000) (-1666991871 / 1000000000000), orderedInterval (-31260084746 / 1000000000000) (-31260084745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1500135549430651 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37970312178 / 1000000000000) (-37970292219 / 1000000000000), orderedInterval (16042935408 / 1000000000000) (16042955367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2662016857328759 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8302820832 / 1000000000000) (8302820833 / 1000000000000), orderedInterval (29787403188 / 1000000000000) (29787403189 / 1000000000000)))) (orderedInterval (-3068051043 / 1000000000000) (-3068048058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2487201455861171 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16730508505 / 1000000000000) (16730508506 / 1000000000000), orderedInterval (27261504107 / 1000000000000) (27261504108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1774984319179043 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37876417534 / 1000000000000) (-37876417186 / 1000000000000), orderedInterval (-115048823 / 1000000000000) (-115048474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2012643038394597 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34187788889 / 1000000000000) (34187788899 / 1000000000000), orderedInterval (9786203103 / 1000000000000) (9786203113 / 1000000000000)))) (orderedInterval (10264104634 / 1000000000000) (10264104805 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1677931936828693 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25255121609 / 1000000000000) (-25255113894 / 1000000000000), orderedInterval (29691668824 / 1000000000000) (29691676539 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1482503752758553 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26796652604 / 1000000000000) (26796652605 / 1000000000000), orderedInterval (31580740413 / 1000000000000) (31580740414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (429687370908747 / 800000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21702370806 / 1000000000000) (-21702370805 / 1000000000000), orderedInterval (-26705773767 / 1000000000000) (-26705773766 / 1000000000000)))) (orderedInterval (5014305482 / 1000000000000) (5014305729 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks2_2 :
    compactCertificate419.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1188537881141009 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23473863092 / 1000000000000) (23473865446 / 1000000000000), orderedInterval (-39933235635 / 1000000000000) (-39933233282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1007536724539849 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48959628180 / 1000000000000) (48959628183 / 1000000000000), orderedInterval (11321258514 / 1000000000000) (11321258517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (630469700786947 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61602503277 / 1000000000000) (61602503278 / 1000000000000), orderedInterval (15429330813 / 1000000000000) (15429330814 / 1000000000000)))) (orderedInterval (5398151520 / 1000000000000) (5398151980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (339068701930749 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57668456427 / 1000000000000) (-57668456426 / 1000000000000), orderedInterval (-64348181839 / 1000000000000) (-64348181838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (920637483999247 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52556350603 / 1000000000000) (-52556350460 / 1000000000000), orderedInterval (2068388480 / 1000000000000) (2068388623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1257051776681519 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34937279227 / 1000000000000) (34937279228 / 1000000000000), orderedInterval (28319422935 / 1000000000000) (28319422936 / 1000000000000)))) (orderedInterval (2301414003 / 1000000000000) (2301414037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (531530299213053 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68445230116 / 1000000000000) (68445230449 / 1000000000000), orderedInterval (-10556210932 / 1000000000000) (-10556210599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2160641156621213 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19143410360 / 1000000000000) (19143410361 / 1000000000000), orderedInterval (28479748140 / 1000000000000) (28479748141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1443208159731667 / 4000000000000) 2 (IntervalRat.scale (581 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12571323072 / 1000000000000) (-12571323071 / 1000000000000), orderedInterval (-40062754190 / 1000000000000) (-40062754189 / 1000000000000)))) (orderedInterval (1645714319 / 1000000000000) (1645714487 / 1000000000000))) = true
  rfl'

theorem compactCertificate419_chunkChecks2 :
    compactCertificate419.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate419.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate419_chunkChecks2_0
    compactCertificate419_chunkChecks2_1 compactCertificate419_chunkChecks2_2

theorem compactCertificate419_chunkChecks3_0 :
    compactCertificate419.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (581 / 2) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36174320395 / 1000000000000) (36174394650 / 1000000000000), orderedInterval (-29775550069 / 1000000000000) (-29775475814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (855923940730481 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49503936443 / 1000000000000) (49503936444 / 1000000000000), orderedInterval (22785814242 / 1000000000000) (22785814243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (276788216365073 / 800000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39903817967 / 1000000000000) (39903817969 / 1000000000000), orderedInterval (15680941053 / 1000000000000) (15680941054 / 1000000000000)))) (orderedInterval (10223952292 / 1000000000000) (10223981855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (249756471200467 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38450459768 / 1000000000000) (38450459769 / 1000000000000), orderedInterval (93060432138 / 1000000000000) (93060432139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (670881012798199 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-56008481920 / 1000000000000) (-56008472167 / 1000000000000), orderedInterval (25833349103 / 1000000000000) (25833358856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1821572454689883 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22547092167 / 1000000000000) (-22547092166 / 1000000000000), orderedInterval (-29801162394 / 1000000000000) (-29801162393 / 1000000000000)))) (orderedInterval (-8321586546 / 1000000000000) (-8321586394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1341762025596979 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3269395744 / 1000000000000) (-3269395743 / 1000000000000), orderedInterval (-43436755175 / 1000000000000) (-43436755174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2299132100461567 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20319200558 / 1000000000000) (-20319200557 / 1000000000000), orderedInterval (-26339732552 / 1000000000000) (-26339732551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1693530299213053 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2041417033 / 1000000000000) (-2041417032 / 1000000000000), orderedInterval (-38720773313 / 1000000000000) (-38720773312 / 1000000000000)))) (orderedInterval (-3387894513 / 1000000000000) (-3387894420 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate419_chunkChecks3_1 :
    compactCertificate419.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2598310989854419 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1666991872 / 1000000000000) (-1666991871 / 1000000000000), orderedInterval (-31260084746 / 1000000000000) (-31260084745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1500135549430651 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37970312178 / 1000000000000) (-37970292219 / 1000000000000), orderedInterval (16042935408 / 1000000000000) (16042955367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2662016857328759 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8302820832 / 1000000000000) (8302820833 / 1000000000000), orderedInterval (29787403188 / 1000000000000) (29787403189 / 1000000000000)))) (orderedInterval (-115559357979 / 1000000000000) (-115559353664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2487201455861171 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16730508505 / 1000000000000) (16730508506 / 1000000000000), orderedInterval (27261504107 / 1000000000000) (27261504108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1774984319179043 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37876417534 / 1000000000000) (-37876417186 / 1000000000000), orderedInterval (-115048823 / 1000000000000) (-115048474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2012643038394597 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34187788889 / 1000000000000) (34187788899 / 1000000000000), orderedInterval (9786203103 / 1000000000000) (9786203113 / 1000000000000)))) (orderedInterval (5087079530 / 1000000000000) (5087079806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1677931936828693 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25255121609 / 1000000000000) (-25255113894 / 1000000000000), orderedInterval (29691668824 / 1000000000000) (29691676539 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1482503752758553 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26796652604 / 1000000000000) (26796652605 / 1000000000000), orderedInterval (31580740413 / 1000000000000) (31580740414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (429687370908747 / 800000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21702370806 / 1000000000000) (-21702370805 / 1000000000000), orderedInterval (-26705773767 / 1000000000000) (-26705773766 / 1000000000000)))) (orderedInterval (7025202911 / 1000000000000) (7025203273 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate419_chunkChecks3_2 :
    compactCertificate419.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1188537881141009 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23473863092 / 1000000000000) (23473865446 / 1000000000000), orderedInterval (-39933235635 / 1000000000000) (-39933233282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1007536724539849 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48959628180 / 1000000000000) (48959628183 / 1000000000000), orderedInterval (11321258514 / 1000000000000) (11321258517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (630469700786947 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61602503277 / 1000000000000) (61602503278 / 1000000000000), orderedInterval (15429330813 / 1000000000000) (15429330814 / 1000000000000)))) (orderedInterval (-6513584175 / 1000000000000) (-6513583708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (339068701930749 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57668456427 / 1000000000000) (-57668456426 / 1000000000000), orderedInterval (-64348181839 / 1000000000000) (-64348181838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (920637483999247 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52556350603 / 1000000000000) (-52556350460 / 1000000000000), orderedInterval (2068388480 / 1000000000000) (2068388623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1257051776681519 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34937279227 / 1000000000000) (34937279228 / 1000000000000), orderedInterval (28319422935 / 1000000000000) (28319422936 / 1000000000000)))) (orderedInterval (2733603417 / 1000000000000) (2733603452 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (531530299213053 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68445230116 / 1000000000000) (68445230449 / 1000000000000), orderedInterval (-10556210932 / 1000000000000) (-10556210599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2160641156621213 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19143410360 / 1000000000000) (19143410361 / 1000000000000), orderedInterval (28479748140 / 1000000000000) (28479748141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1443208159731667 / 4000000000000) 3 (IntervalRat.scale (581 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12571323072 / 1000000000000) (-12571323071 / 1000000000000), orderedInterval (-40062754190 / 1000000000000) (-40062754189 / 1000000000000)))) (orderedInterval (503010149 / 1000000000000) (503010408 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate419_chunkChecks3 :
    compactCertificate419.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate419.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate419_chunkChecks3_0
    compactCertificate419_chunkChecks3_1 compactCertificate419_chunkChecks3_2

theorem compactCertificate419_chunkChecks4_0 :
    compactCertificate419.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (581 / 2) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36174320395 / 1000000000000) (36174394650 / 1000000000000), orderedInterval (-29775550069 / 1000000000000) (-29775475814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (855923940730481 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49503936443 / 1000000000000) (49503936444 / 1000000000000), orderedInterval (22785814242 / 1000000000000) (22785814243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (276788216365073 / 800000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39903817967 / 1000000000000) (39903817969 / 1000000000000), orderedInterval (15680941053 / 1000000000000) (15680941054 / 1000000000000)))) (orderedInterval (19114924915 / 1000000000000) (19114954585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (249756471200467 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38450459768 / 1000000000000) (38450459769 / 1000000000000), orderedInterval (93060432138 / 1000000000000) (93060432139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (670881012798199 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-56008481920 / 1000000000000) (-56008472167 / 1000000000000), orderedInterval (25833349103 / 1000000000000) (25833358856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1821572454689883 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-22547092167 / 1000000000000) (-22547092166 / 1000000000000), orderedInterval (-29801162394 / 1000000000000) (-29801162393 / 1000000000000)))) (orderedInterval (9508760300 / 1000000000000) (9508760468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1341762025596979 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-3269395744 / 1000000000000) (-3269395743 / 1000000000000), orderedInterval (-43436755175 / 1000000000000) (-43436755174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2299132100461567 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20319200558 / 1000000000000) (-20319200557 / 1000000000000), orderedInterval (-26339732552 / 1000000000000) (-26339732551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1693530299213053 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2041417033 / 1000000000000) (-2041417032 / 1000000000000), orderedInterval (-38720773313 / 1000000000000) (-38720773312 / 1000000000000)))) (orderedInterval (9405945605 / 1000000000000) (9405945776 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate419_chunkChecks4_1 :
    compactCertificate419.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2598310989854419 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-1666991872 / 1000000000000) (-1666991871 / 1000000000000), orderedInterval (-31260084746 / 1000000000000) (-31260084745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1500135549430651 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37970312178 / 1000000000000) (-37970292219 / 1000000000000), orderedInterval (16042935408 / 1000000000000) (16042955367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2662016857328759 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8302820832 / 1000000000000) (8302820833 / 1000000000000), orderedInterval (29787403188 / 1000000000000) (29787403189 / 1000000000000)))) (orderedInterval (32895391231 / 1000000000000) (32895397858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2487201455861171 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16730508505 / 1000000000000) (16730508506 / 1000000000000), orderedInterval (27261504107 / 1000000000000) (27261504108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1774984319179043 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37876417534 / 1000000000000) (-37876417186 / 1000000000000), orderedInterval (-115048823 / 1000000000000) (-115048474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2012643038394597 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34187788889 / 1000000000000) (34187788899 / 1000000000000), orderedInterval (9786203103 / 1000000000000) (9786203113 / 1000000000000)))) (orderedInterval (-27432235194 / 1000000000000) (-27432234739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1677931936828693 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25255121609 / 1000000000000) (-25255113894 / 1000000000000), orderedInterval (29691668824 / 1000000000000) (29691676539 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1482503752758553 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26796652604 / 1000000000000) (26796652605 / 1000000000000), orderedInterval (31580740413 / 1000000000000) (31580740414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (429687370908747 / 800000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21702370806 / 1000000000000) (-21702370805 / 1000000000000), orderedInterval (-26705773767 / 1000000000000) (-26705773766 / 1000000000000)))) (orderedInterval (-11872732046 / 1000000000000) (-11872731510 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate419_chunkChecks4_2 :
    compactCertificate419.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1188537881141009 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23473863092 / 1000000000000) (23473865446 / 1000000000000), orderedInterval (-39933235635 / 1000000000000) (-39933233282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1007536724539849 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48959628180 / 1000000000000) (48959628183 / 1000000000000), orderedInterval (11321258514 / 1000000000000) (11321258517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (630469700786947 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61602503277 / 1000000000000) (61602503278 / 1000000000000), orderedInterval (15429330813 / 1000000000000) (15429330814 / 1000000000000)))) (orderedInterval (-5455677138 / 1000000000000) (-5455676661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (339068701930749 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57668456427 / 1000000000000) (-57668456426 / 1000000000000), orderedInterval (-64348181839 / 1000000000000) (-64348181838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (920637483999247 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52556350603 / 1000000000000) (-52556350460 / 1000000000000), orderedInterval (2068388480 / 1000000000000) (2068388623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1257051776681519 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34937279227 / 1000000000000) (34937279228 / 1000000000000), orderedInterval (28319422935 / 1000000000000) (28319422936 / 1000000000000)))) (orderedInterval (-3208384748 / 1000000000000) (-3208384712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (531530299213053 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68445230116 / 1000000000000) (68445230449 / 1000000000000), orderedInterval (-10556210932 / 1000000000000) (-10556210599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2160641156621213 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19143410360 / 1000000000000) (19143410361 / 1000000000000), orderedInterval (28479748140 / 1000000000000) (28479748141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1443208159731667 / 4000000000000) 4 (IntervalRat.scale (581 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12571323072 / 1000000000000) (-12571323071 / 1000000000000), orderedInterval (-40062754190 / 1000000000000) (-40062754189 / 1000000000000)))) (orderedInterval (-13000447842 / 1000000000000) (-13000447427 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate419_chunkChecks4 :
    compactCertificate419.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate419.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate419_chunkChecks4_0
    compactCertificate419_chunkChecks4_1 compactCertificate419_chunkChecks4_2

theorem compactCertificate419_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate419.chunkCheck r b = true :=
  compactCertificate419.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate419_chunkChecks0
    · exact compactCertificate419_chunkChecks1
    · exact compactCertificate419_chunkChecks2
    · exact compactCertificate419_chunkChecks3
    · exact compactCertificate419_chunkChecks4)

theorem compactCertificate419_coefficient0 :
    compactCertificate419.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate419_coefficient1 :
    compactCertificate419.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate419_coefficient2 :
    compactCertificate419.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate419_coefficient3 :
    compactCertificate419.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate419_coefficient4 :
    compactCertificate419.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate419_coefficients : ∀ r : Fin 5,
    compactCertificate419.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate419_coefficient0
  · exact compactCertificate419_coefficient1
  · exact compactCertificate419_coefficient2
  · exact compactCertificate419_coefficient3
  · exact compactCertificate419_coefficient4

theorem compactCertificate419_lower : (1 : ℚ) ≤ compactCertificate419.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate419, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate419_proves {t : ℝ} (ht : t ∈ compactCertificate419.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate419.proves compactCertificate419_states compactCertificate419_chunks
    compactCertificate419_coefficients compactCertificate419_lower ht

end Erdos232
