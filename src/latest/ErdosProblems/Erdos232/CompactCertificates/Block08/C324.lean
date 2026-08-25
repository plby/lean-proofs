/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate324 : CompactCertificate where
  left := 196
  right := 197
  center := 393 / 2
  grid := fun i =>
    match i.val with
    | 0 => 63
    | 1 => 46
    | 2 => 75
    | 3 => 13
    | 4 => 36
    | 5 => 98
    | 6 => 72
    | 7 => 124
    | 8 => 91
    | 9 => 140
    | 10 => 81
    | 11 => 143
    | 12 => 134
    | 13 => 96
    | 14 => 108
    | 15 => 90
    | 16 => 80
    | 17 => 116
    | 18 => 64
    | 19 => 54
    | 20 => 34
    | 21 => 18
    | 22 => 50
    | 23 => 68
    | 24 => 29
    | 25 => 116
    | _ => 78
  point := fun i =>
    match i.val with
    | 0 => 393 / 2
    | 1 => 578964042525093 / 4000000000000
    | 2 => 187225075785669 / 800000000000
    | 3 => 168940263651951 / 4000000000000
    | 4 => 453797311582947 / 4000000000000
    | 5 => 1232147977096599 / 4000000000000
    | 6 => 907594623166287 / 4000000000000
    | 7 => 1555178856250251 / 4000000000000
    | 8 => 1145537706696609 / 4000000000000
    | 9 => 1757549430314607 / 4000000000000
    | 10 => 1014721636706103 / 4000000000000
    | 11 => 1800641350998627 / 4000000000000
    | 12 => 1682392723155663 / 4000000000000
    | 13 => 1200634832078079 / 4000000000000
    | 14 => 1361391934748841 / 4000000000000
    | 15 => 1134986662949529 / 4000000000000
    | 16 => 1002795137408109 / 4000000000000
    | 17 => 290649116638791 / 800000000000
    | 18 => 803950752647877 / 4000000000000
    | 19 => 681517956530397 / 4000000000000
    | 20 => 426462293303391 / 4000000000000
    | 21 => 229352839688097 / 4000000000000
    | 22 => 622737575235291 / 4000000000000
    | 23 => 850294919510907 / 4000000000000
    | 24 => 359537706696609 / 4000000000000
    | 25 => 1461500816785089 / 4000000000000
    | _ => 976214813725551 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (33789477912 / 1000000000000) (33789489777 / 1000000000000), orderedInterval (-45890668186 / 1000000000000) (-45890656321 / 1000000000000))
    | 1 => (orderedInterval (56242073694 / 1000000000000) (56242073695 / 1000000000000), orderedInterval (34950486996 / 1000000000000) (34950486997 / 1000000000000))
    | 2 => (orderedInterval (37531795668 / 1000000000000) (37531843171 / 1000000000000), orderedInterval (-36296160036 / 1000000000000) (-36296112534 / 1000000000000))
    | 3 => (orderedInterval (-100907478921 / 1000000000000) (-100907449622 / 1000000000000), orderedInterval (71126981148 / 1000000000000) (71127010448 / 1000000000000))
    | 4 => (orderedInterval (67948732399 / 1000000000000) (67948732400 / 1000000000000), orderedInterval (31235037328 / 1000000000000) (31235037329 / 1000000000000))
    | 5 => (orderedInterval (36870072134 / 1000000000000) (36870072135 / 1000000000000), orderedInterval (26535190477 / 1000000000000) (26535190478 / 1000000000000))
    | 6 => (orderedInterval (52791391343 / 1000000000000) (52791391368 / 1000000000000), orderedInterval (4220405596 / 1000000000000) (4220405621 / 1000000000000))
    | 7 => (orderedInterval (902362829 / 1000000000000) (902362830 / 1000000000000), orderedInterval (40453825504 / 1000000000000) (40453825506 / 1000000000000))
    | 8 => (orderedInterval (-45228514352 / 1000000000000) (-45228514350 / 1000000000000), orderedInterval (-13237713767 / 1000000000000) (-13237713765 / 1000000000000))
    | 9 => (orderedInterval (13034225099 / 1000000000000) (13034225100 / 1000000000000), orderedInterval (35748140074 / 1000000000000) (35748140075 / 1000000000000))
    | 10 => (orderedInterval (184868067 / 1000000000000) (184868070 / 1000000000000), orderedInterval (-50095327495 / 1000000000000) (-50095327493 / 1000000000000))
    | 11 => (orderedInterval (-37303480438 / 1000000000000) (-37303478666 / 1000000000000), orderedInterval (4801294116 / 1000000000000) (4801295888 / 1000000000000))
    | 12 => (orderedInterval (15503149185 / 1000000000000) (15503149186 / 1000000000000), orderedInterval (35664321164 / 1000000000000) (35664321165 / 1000000000000))
    | 13 => (orderedInterval (-27841906226 / 1000000000000) (-27841898168 / 1000000000000), orderedInterval (36731155105 / 1000000000000) (36731163163 / 1000000000000))
    | 14 => (orderedInterval (41679890278 / 1000000000000) (41679894916 / 1000000000000), orderedInterval (-11605993807 / 1000000000000) (-11605989169 / 1000000000000))
    | 15 => (orderedInterval (46250987776 / 1000000000000) (46250989680 / 1000000000000), orderedInterval (-10302223023 / 1000000000000) (-10302221119 / 1000000000000))
    | 16 => (orderedInterval (7842861895 / 1000000000000) (7842861896 / 1000000000000), orderedInterval (49762621319 / 1000000000000) (49762621320 / 1000000000000))
    | 17 => (orderedInterval (-13497051465 / 1000000000000) (-13497051341 / 1000000000000), orderedInterval (39643077825 / 1000000000000) (39643077949 / 1000000000000))
    | 18 => (orderedInterval (36708063842 / 1000000000000) (36708063843 / 1000000000000), orderedInterval (42569859000 / 1000000000000) (42569859001 / 1000000000000))
    | 19 => (orderedInterval (61041942786 / 1000000000000) (61041942811 / 1000000000000), orderedInterval (3037464538 / 1000000000000) (3037464563 / 1000000000000))
    | 20 => (orderedInterval (42711855657 / 1000000000000) (42711855658 / 1000000000000), orderedInterval (64196074486 / 1000000000000) (64196074487 / 1000000000000))
    | 21 => (orderedInterval (105368041157 / 1000000000000) (105368041181 / 1000000000000), orderedInterval (-1125741116 / 1000000000000) (-1125741092 / 1000000000000))
    | 22 => (orderedInterval (-36666568197 / 1000000000000) (-36666556836 / 1000000000000), orderedInterval (52508011137 / 1000000000000) (52508022498 / 1000000000000))
    | 23 => (orderedInterval (-14584204773 / 1000000000000) (-14584204615 / 1000000000000), orderedInterval (52780172999 / 1000000000000) (52780173157 / 1000000000000))
    | 24 => (orderedInterval (35674931357 / 1000000000000) (35674933988 / 1000000000000), orderedInterval (-76421915161 / 1000000000000) (-76421912530 / 1000000000000))
    | 25 => (orderedInterval (41176741014 / 1000000000000) (41176742685 / 1000000000000), orderedInterval (-6900840567 / 1000000000000) (-6900838896 / 1000000000000))
    | _ => (orderedInterval (-10428796837 / 1000000000000) (-10428796786 / 1000000000000), orderedInterval (50019050782 / 1000000000000) (50019050833 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16119441742 / 1000000000000) (16119449247 / 1000000000000)
      | 1 => orderedInterval (954620940 / 1000000000000) (954621282 / 1000000000000)
      | 2 => orderedInterval (-1120916442 / 1000000000000) (-1120916430 / 1000000000000)
      | 3 => orderedInterval (-7605236798 / 1000000000000) (-7605236467 / 1000000000000)
      | 4 => orderedInterval (-3123614421 / 1000000000000) (-3123613612 / 1000000000000)
      | 5 => orderedInterval (-260307621 / 1000000000000) (-260307576 / 1000000000000)
      | 6 => orderedInterval (-7933817235 / 1000000000000) (-7933817184 / 1000000000000)
      | 7 => orderedInterval (3932856 / 1000000000000) (3933150 / 1000000000000)
      | _ => orderedInterval (-1180080944 / 1000000000000) (-1180080727 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-20486276068 / 1000000000000) (-20486268029 / 1000000000000)
      | 1 => orderedInterval (-2464544563 / 1000000000000) (-2464544467 / 1000000000000)
      | 2 => orderedInterval (-2935086295 / 1000000000000) (-2935086275 / 1000000000000)
      | 3 => orderedInterval (-17431646299 / 1000000000000) (-17431645560 / 1000000000000)
      | 4 => orderedInterval (4029309487 / 1000000000000) (4029310730 / 1000000000000)
      | 5 => orderedInterval (-1928323754 / 1000000000000) (-1928323688 / 1000000000000)
      | 6 => orderedInterval (-5977181495 / 1000000000000) (-5977181447 / 1000000000000)
      | 7 => orderedInterval (-5313635673 / 1000000000000) (-5313635434 / 1000000000000)
      | _ => orderedInterval (-10822306176 / 1000000000000) (-10822305827 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16697134128 / 1000000000000) (-16697125412 / 1000000000000)
      | 1 => orderedInterval (5576103915 / 1000000000000) (5576103968 / 1000000000000)
      | 2 => orderedInterval (2445709736 / 1000000000000) (2445709771 / 1000000000000)
      | 3 => orderedInterval (39476666424 / 1000000000000) (39476668097 / 1000000000000)
      | 4 => orderedInterval (8037764551 / 1000000000000) (8037766469 / 1000000000000)
      | 5 => orderedInterval (808060177 / 1000000000000) (808060275 / 1000000000000)
      | 6 => orderedInterval (8359059598 / 1000000000000) (8359059643 / 1000000000000)
      | 7 => orderedInterval (-1637518282 / 1000000000000) (-1637518083 / 1000000000000)
      | _ => orderedInterval (8580505852 / 1000000000000) (8580506455 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (21741999668 / 1000000000000) (21742009144 / 1000000000000)
      | 1 => orderedInterval (7026647834 / 1000000000000) (7026647894 / 1000000000000)
      | 2 => orderedInterval (10642927808 / 1000000000000) (10642927871 / 1000000000000)
      | 3 => orderedInterval (70596404066 / 1000000000000) (70596407863 / 1000000000000)
      | 4 => orderedInterval (-6412049253 / 1000000000000) (-6412046298 / 1000000000000)
      | 5 => orderedInterval (-147501902 / 1000000000000) (-147501752 / 1000000000000)
      | 6 => orderedInterval (7019242211 / 1000000000000) (7019242255 / 1000000000000)
      | 7 => orderedInterval (5721197294 / 1000000000000) (5721197461 / 1000000000000)
      | _ => orderedInterval (14369185163 / 1000000000000) (14369186234 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (17756950200 / 1000000000000) (17756960632 / 1000000000000)
      | 1 => orderedInterval (-15621945258 / 1000000000000) (-15621945171 / 1000000000000)
      | 2 => orderedInterval (-5466572379 / 1000000000000) (-5466572263 / 1000000000000)
      | 3 => orderedInterval (-204640620736 / 1000000000000) (-204640612078 / 1000000000000)
      | 4 => orderedInterval (-22041806563 / 1000000000000) (-22041801988 / 1000000000000)
      | 5 => orderedInterval (-2903897576 / 1000000000000) (-2903897343 / 1000000000000)
      | 6 => orderedInterval (-8327716715 / 1000000000000) (-8327716672 / 1000000000000)
      | 7 => orderedInterval (1786201351 / 1000000000000) (1786201494 / 1000000000000)
      | _ => orderedInterval (-35548010342 / 1000000000000) (-35548008403 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-4145977923 / 1000000000000) (-4145968317 / 1000000000000)
    | 1 => orderedInterval (-63329690836 / 1000000000000) (-63329679997 / 1000000000000)
    | 2 => orderedInterval (54949217843 / 1000000000000) (54949231183 / 1000000000000)
    | 3 => orderedInterval (130558052889 / 1000000000000) (130558070672 / 1000000000000)
    | _ => orderedInterval (-275007418018 / 1000000000000) (-275007391792 / 1000000000000)

theorem compactCertificate324_stateChecks0 :
    compactCertificate324.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (393 / 2)) (orderedInterval (33789477912 / 1000000000000) (33789489777 / 1000000000000), orderedInterval (-45890668186 / 1000000000000) (-45890656321 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (578964042525093 / 4000000000000)) (orderedInterval (56242073694 / 1000000000000) (56242073695 / 1000000000000), orderedInterval (34950486996 / 1000000000000) (34950486997 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (187225075785669 / 800000000000)) (orderedInterval (37531795668 / 1000000000000) (37531843171 / 1000000000000), orderedInterval (-36296160036 / 1000000000000) (-36296112534 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_stateChecks1 :
    compactCertificate324.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (168940263651951 / 4000000000000)) (orderedInterval (-100907478921 / 1000000000000) (-100907449622 / 1000000000000), orderedInterval (71126981148 / 1000000000000) (71127010448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (453797311582947 / 4000000000000)) (orderedInterval (67948732399 / 1000000000000) (67948732400 / 1000000000000), orderedInterval (31235037328 / 1000000000000) (31235037329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1232147977096599 / 4000000000000)) (orderedInterval (36870072134 / 1000000000000) (36870072135 / 1000000000000), orderedInterval (26535190477 / 1000000000000) (26535190478 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_stateChecks2 :
    compactCertificate324.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (907594623166287 / 4000000000000)) (orderedInterval (52791391343 / 1000000000000) (52791391368 / 1000000000000), orderedInterval (4220405596 / 1000000000000) (4220405621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1555178856250251 / 4000000000000)) (orderedInterval (902362829 / 1000000000000) (902362830 / 1000000000000), orderedInterval (40453825504 / 1000000000000) (40453825506 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1145537706696609 / 4000000000000)) (orderedInterval (-45228514352 / 1000000000000) (-45228514350 / 1000000000000), orderedInterval (-13237713767 / 1000000000000) (-13237713765 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_stateChecks3 :
    compactCertificate324.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1757549430314607 / 4000000000000)) (orderedInterval (13034225099 / 1000000000000) (13034225100 / 1000000000000), orderedInterval (35748140074 / 1000000000000) (35748140075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1014721636706103 / 4000000000000)) (orderedInterval (184868067 / 1000000000000) (184868070 / 1000000000000), orderedInterval (-50095327495 / 1000000000000) (-50095327493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1800641350998627 / 4000000000000)) (orderedInterval (-37303480438 / 1000000000000) (-37303478666 / 1000000000000), orderedInterval (4801294116 / 1000000000000) (4801295888 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_stateChecks4 :
    compactCertificate324.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1682392723155663 / 4000000000000)) (orderedInterval (15503149185 / 1000000000000) (15503149186 / 1000000000000), orderedInterval (35664321164 / 1000000000000) (35664321165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1200634832078079 / 4000000000000)) (orderedInterval (-27841906226 / 1000000000000) (-27841898168 / 1000000000000), orderedInterval (36731155105 / 1000000000000) (36731163163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1361391934748841 / 4000000000000)) (orderedInterval (41679890278 / 1000000000000) (41679894916 / 1000000000000), orderedInterval (-11605993807 / 1000000000000) (-11605989169 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_stateChecks5 :
    compactCertificate324.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1134986662949529 / 4000000000000)) (orderedInterval (46250987776 / 1000000000000) (46250989680 / 1000000000000), orderedInterval (-10302223023 / 1000000000000) (-10302221119 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1002795137408109 / 4000000000000)) (orderedInterval (7842861895 / 1000000000000) (7842861896 / 1000000000000), orderedInterval (49762621319 / 1000000000000) (49762621320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (290649116638791 / 800000000000)) (orderedInterval (-13497051465 / 1000000000000) (-13497051341 / 1000000000000), orderedInterval (39643077825 / 1000000000000) (39643077949 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_stateChecks6 :
    compactCertificate324.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (803950752647877 / 4000000000000)) (orderedInterval (36708063842 / 1000000000000) (36708063843 / 1000000000000), orderedInterval (42569859000 / 1000000000000) (42569859001 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (681517956530397 / 4000000000000)) (orderedInterval (61041942786 / 1000000000000) (61041942811 / 1000000000000), orderedInterval (3037464538 / 1000000000000) (3037464563 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (426462293303391 / 4000000000000)) (orderedInterval (42711855657 / 1000000000000) (42711855658 / 1000000000000), orderedInterval (64196074486 / 1000000000000) (64196074487 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_stateChecks7 :
    compactCertificate324.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (229352839688097 / 4000000000000)) (orderedInterval (105368041157 / 1000000000000) (105368041181 / 1000000000000), orderedInterval (-1125741116 / 1000000000000) (-1125741092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (622737575235291 / 4000000000000)) (orderedInterval (-36666568197 / 1000000000000) (-36666556836 / 1000000000000), orderedInterval (52508011137 / 1000000000000) (52508022498 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (850294919510907 / 4000000000000)) (orderedInterval (-14584204773 / 1000000000000) (-14584204615 / 1000000000000), orderedInterval (52780172999 / 1000000000000) (52780173157 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_stateChecks8 :
    compactCertificate324.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (359537706696609 / 4000000000000)) (orderedInterval (35674931357 / 1000000000000) (35674933988 / 1000000000000), orderedInterval (-76421915161 / 1000000000000) (-76421912530 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1461500816785089 / 4000000000000)) (orderedInterval (41176741014 / 1000000000000) (41176742685 / 1000000000000), orderedInterval (-6900840567 / 1000000000000) (-6900838896 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (976214813725551 / 4000000000000)) (orderedInterval (-10428796837 / 1000000000000) (-10428796786 / 1000000000000), orderedInterval (50019050782 / 1000000000000) (50019050833 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_states : ∀ j,
    BesselStateValid (compactCertificate324.point j) (compactCertificate324.state j) :=
  compactCertificate324.statesValid_of_checks3 compactCertificate324_stateChecks0
    compactCertificate324_stateChecks1 compactCertificate324_stateChecks2
    compactCertificate324_stateChecks3 compactCertificate324_stateChecks4
    compactCertificate324_stateChecks5 compactCertificate324_stateChecks6
    compactCertificate324_stateChecks7 compactCertificate324_stateChecks8

theorem compactCertificate324_chunkChecks0_0 :
    compactCertificate324.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (393 / 2) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33789477912 / 1000000000000) (33789489777 / 1000000000000), orderedInterval (-45890668186 / 1000000000000) (-45890656321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (578964042525093 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56242073694 / 1000000000000) (56242073695 / 1000000000000), orderedInterval (34950486996 / 1000000000000) (34950486997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (187225075785669 / 800000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37531795668 / 1000000000000) (37531843171 / 1000000000000), orderedInterval (-36296160036 / 1000000000000) (-36296112534 / 1000000000000)))) (orderedInterval (16119441742 / 1000000000000) (16119449247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (168940263651951 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100907478921 / 1000000000000) (-100907449622 / 1000000000000), orderedInterval (71126981148 / 1000000000000) (71127010448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (453797311582947 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67948732399 / 1000000000000) (67948732400 / 1000000000000), orderedInterval (31235037328 / 1000000000000) (31235037329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1232147977096599 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36870072134 / 1000000000000) (36870072135 / 1000000000000), orderedInterval (26535190477 / 1000000000000) (26535190478 / 1000000000000)))) (orderedInterval (954620940 / 1000000000000) (954621282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (907594623166287 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52791391343 / 1000000000000) (52791391368 / 1000000000000), orderedInterval (4220405596 / 1000000000000) (4220405621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1555178856250251 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (902362829 / 1000000000000) (902362830 / 1000000000000), orderedInterval (40453825504 / 1000000000000) (40453825506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1145537706696609 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45228514352 / 1000000000000) (-45228514350 / 1000000000000), orderedInterval (-13237713767 / 1000000000000) (-13237713765 / 1000000000000)))) (orderedInterval (-1120916442 / 1000000000000) (-1120916430 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks0_1 :
    compactCertificate324.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1757549430314607 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13034225099 / 1000000000000) (13034225100 / 1000000000000), orderedInterval (35748140074 / 1000000000000) (35748140075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1014721636706103 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (184868067 / 1000000000000) (184868070 / 1000000000000), orderedInterval (-50095327495 / 1000000000000) (-50095327493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1800641350998627 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-37303480438 / 1000000000000) (-37303478666 / 1000000000000), orderedInterval (4801294116 / 1000000000000) (4801295888 / 1000000000000)))) (orderedInterval (-7605236798 / 1000000000000) (-7605236467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1682392723155663 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15503149185 / 1000000000000) (15503149186 / 1000000000000), orderedInterval (35664321164 / 1000000000000) (35664321165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1200634832078079 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27841906226 / 1000000000000) (-27841898168 / 1000000000000), orderedInterval (36731155105 / 1000000000000) (36731163163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1361391934748841 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41679890278 / 1000000000000) (41679894916 / 1000000000000), orderedInterval (-11605993807 / 1000000000000) (-11605989169 / 1000000000000)))) (orderedInterval (-3123614421 / 1000000000000) (-3123613612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1134986662949529 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46250987776 / 1000000000000) (46250989680 / 1000000000000), orderedInterval (-10302223023 / 1000000000000) (-10302221119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1002795137408109 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7842861895 / 1000000000000) (7842861896 / 1000000000000), orderedInterval (49762621319 / 1000000000000) (49762621320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (290649116638791 / 800000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13497051465 / 1000000000000) (-13497051341 / 1000000000000), orderedInterval (39643077825 / 1000000000000) (39643077949 / 1000000000000)))) (orderedInterval (-260307621 / 1000000000000) (-260307576 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks0_2 :
    compactCertificate324.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (803950752647877 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36708063842 / 1000000000000) (36708063843 / 1000000000000), orderedInterval (42569859000 / 1000000000000) (42569859001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (681517956530397 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61041942786 / 1000000000000) (61041942811 / 1000000000000), orderedInterval (3037464538 / 1000000000000) (3037464563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (426462293303391 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42711855657 / 1000000000000) (42711855658 / 1000000000000), orderedInterval (64196074486 / 1000000000000) (64196074487 / 1000000000000)))) (orderedInterval (-7933817235 / 1000000000000) (-7933817184 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (229352839688097 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (105368041157 / 1000000000000) (105368041181 / 1000000000000), orderedInterval (-1125741116 / 1000000000000) (-1125741092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (622737575235291 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36666568197 / 1000000000000) (-36666556836 / 1000000000000), orderedInterval (52508011137 / 1000000000000) (52508022498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (850294919510907 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14584204773 / 1000000000000) (-14584204615 / 1000000000000), orderedInterval (52780172999 / 1000000000000) (52780173157 / 1000000000000)))) (orderedInterval (3932856 / 1000000000000) (3933150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (359537706696609 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35674931357 / 1000000000000) (35674933988 / 1000000000000), orderedInterval (-76421915161 / 1000000000000) (-76421912530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1461500816785089 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41176741014 / 1000000000000) (41176742685 / 1000000000000), orderedInterval (-6900840567 / 1000000000000) (-6900838896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (976214813725551 / 4000000000000) 0 (IntervalRat.scale (393 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10428796837 / 1000000000000) (-10428796786 / 1000000000000), orderedInterval (50019050782 / 1000000000000) (50019050833 / 1000000000000)))) (orderedInterval (-1180080944 / 1000000000000) (-1180080727 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks0 :
    compactCertificate324.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate324.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate324_chunkChecks0_0
    compactCertificate324_chunkChecks0_1 compactCertificate324_chunkChecks0_2

theorem compactCertificate324_chunkChecks1_0 :
    compactCertificate324.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (393 / 2) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33789477912 / 1000000000000) (33789489777 / 1000000000000), orderedInterval (-45890668186 / 1000000000000) (-45890656321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (578964042525093 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56242073694 / 1000000000000) (56242073695 / 1000000000000), orderedInterval (34950486996 / 1000000000000) (34950486997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (187225075785669 / 800000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37531795668 / 1000000000000) (37531843171 / 1000000000000), orderedInterval (-36296160036 / 1000000000000) (-36296112534 / 1000000000000)))) (orderedInterval (-20486276068 / 1000000000000) (-20486268029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (168940263651951 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100907478921 / 1000000000000) (-100907449622 / 1000000000000), orderedInterval (71126981148 / 1000000000000) (71127010448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (453797311582947 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67948732399 / 1000000000000) (67948732400 / 1000000000000), orderedInterval (31235037328 / 1000000000000) (31235037329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1232147977096599 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36870072134 / 1000000000000) (36870072135 / 1000000000000), orderedInterval (26535190477 / 1000000000000) (26535190478 / 1000000000000)))) (orderedInterval (-2464544563 / 1000000000000) (-2464544467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (907594623166287 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52791391343 / 1000000000000) (52791391368 / 1000000000000), orderedInterval (4220405596 / 1000000000000) (4220405621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1555178856250251 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (902362829 / 1000000000000) (902362830 / 1000000000000), orderedInterval (40453825504 / 1000000000000) (40453825506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1145537706696609 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45228514352 / 1000000000000) (-45228514350 / 1000000000000), orderedInterval (-13237713767 / 1000000000000) (-13237713765 / 1000000000000)))) (orderedInterval (-2935086295 / 1000000000000) (-2935086275 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks1_1 :
    compactCertificate324.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1757549430314607 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13034225099 / 1000000000000) (13034225100 / 1000000000000), orderedInterval (35748140074 / 1000000000000) (35748140075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1014721636706103 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (184868067 / 1000000000000) (184868070 / 1000000000000), orderedInterval (-50095327495 / 1000000000000) (-50095327493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1800641350998627 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-37303480438 / 1000000000000) (-37303478666 / 1000000000000), orderedInterval (4801294116 / 1000000000000) (4801295888 / 1000000000000)))) (orderedInterval (-17431646299 / 1000000000000) (-17431645560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1682392723155663 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15503149185 / 1000000000000) (15503149186 / 1000000000000), orderedInterval (35664321164 / 1000000000000) (35664321165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1200634832078079 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27841906226 / 1000000000000) (-27841898168 / 1000000000000), orderedInterval (36731155105 / 1000000000000) (36731163163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1361391934748841 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41679890278 / 1000000000000) (41679894916 / 1000000000000), orderedInterval (-11605993807 / 1000000000000) (-11605989169 / 1000000000000)))) (orderedInterval (4029309487 / 1000000000000) (4029310730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1134986662949529 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46250987776 / 1000000000000) (46250989680 / 1000000000000), orderedInterval (-10302223023 / 1000000000000) (-10302221119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1002795137408109 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7842861895 / 1000000000000) (7842861896 / 1000000000000), orderedInterval (49762621319 / 1000000000000) (49762621320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (290649116638791 / 800000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13497051465 / 1000000000000) (-13497051341 / 1000000000000), orderedInterval (39643077825 / 1000000000000) (39643077949 / 1000000000000)))) (orderedInterval (-1928323754 / 1000000000000) (-1928323688 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks1_2 :
    compactCertificate324.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (803950752647877 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36708063842 / 1000000000000) (36708063843 / 1000000000000), orderedInterval (42569859000 / 1000000000000) (42569859001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (681517956530397 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61041942786 / 1000000000000) (61041942811 / 1000000000000), orderedInterval (3037464538 / 1000000000000) (3037464563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (426462293303391 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42711855657 / 1000000000000) (42711855658 / 1000000000000), orderedInterval (64196074486 / 1000000000000) (64196074487 / 1000000000000)))) (orderedInterval (-5977181495 / 1000000000000) (-5977181447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (229352839688097 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (105368041157 / 1000000000000) (105368041181 / 1000000000000), orderedInterval (-1125741116 / 1000000000000) (-1125741092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (622737575235291 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36666568197 / 1000000000000) (-36666556836 / 1000000000000), orderedInterval (52508011137 / 1000000000000) (52508022498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (850294919510907 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14584204773 / 1000000000000) (-14584204615 / 1000000000000), orderedInterval (52780172999 / 1000000000000) (52780173157 / 1000000000000)))) (orderedInterval (-5313635673 / 1000000000000) (-5313635434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (359537706696609 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35674931357 / 1000000000000) (35674933988 / 1000000000000), orderedInterval (-76421915161 / 1000000000000) (-76421912530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1461500816785089 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41176741014 / 1000000000000) (41176742685 / 1000000000000), orderedInterval (-6900840567 / 1000000000000) (-6900838896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (976214813725551 / 4000000000000) 1 (IntervalRat.scale (393 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10428796837 / 1000000000000) (-10428796786 / 1000000000000), orderedInterval (50019050782 / 1000000000000) (50019050833 / 1000000000000)))) (orderedInterval (-10822306176 / 1000000000000) (-10822305827 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks1 :
    compactCertificate324.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate324.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate324_chunkChecks1_0
    compactCertificate324_chunkChecks1_1 compactCertificate324_chunkChecks1_2

theorem compactCertificate324_chunkChecks2_0 :
    compactCertificate324.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (393 / 2) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33789477912 / 1000000000000) (33789489777 / 1000000000000), orderedInterval (-45890668186 / 1000000000000) (-45890656321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (578964042525093 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56242073694 / 1000000000000) (56242073695 / 1000000000000), orderedInterval (34950486996 / 1000000000000) (34950486997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (187225075785669 / 800000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37531795668 / 1000000000000) (37531843171 / 1000000000000), orderedInterval (-36296160036 / 1000000000000) (-36296112534 / 1000000000000)))) (orderedInterval (-16697134128 / 1000000000000) (-16697125412 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (168940263651951 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100907478921 / 1000000000000) (-100907449622 / 1000000000000), orderedInterval (71126981148 / 1000000000000) (71127010448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (453797311582947 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67948732399 / 1000000000000) (67948732400 / 1000000000000), orderedInterval (31235037328 / 1000000000000) (31235037329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1232147977096599 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36870072134 / 1000000000000) (36870072135 / 1000000000000), orderedInterval (26535190477 / 1000000000000) (26535190478 / 1000000000000)))) (orderedInterval (5576103915 / 1000000000000) (5576103968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (907594623166287 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52791391343 / 1000000000000) (52791391368 / 1000000000000), orderedInterval (4220405596 / 1000000000000) (4220405621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1555178856250251 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (902362829 / 1000000000000) (902362830 / 1000000000000), orderedInterval (40453825504 / 1000000000000) (40453825506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1145537706696609 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45228514352 / 1000000000000) (-45228514350 / 1000000000000), orderedInterval (-13237713767 / 1000000000000) (-13237713765 / 1000000000000)))) (orderedInterval (2445709736 / 1000000000000) (2445709771 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks2_1 :
    compactCertificate324.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1757549430314607 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13034225099 / 1000000000000) (13034225100 / 1000000000000), orderedInterval (35748140074 / 1000000000000) (35748140075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1014721636706103 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (184868067 / 1000000000000) (184868070 / 1000000000000), orderedInterval (-50095327495 / 1000000000000) (-50095327493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1800641350998627 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-37303480438 / 1000000000000) (-37303478666 / 1000000000000), orderedInterval (4801294116 / 1000000000000) (4801295888 / 1000000000000)))) (orderedInterval (39476666424 / 1000000000000) (39476668097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1682392723155663 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15503149185 / 1000000000000) (15503149186 / 1000000000000), orderedInterval (35664321164 / 1000000000000) (35664321165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1200634832078079 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27841906226 / 1000000000000) (-27841898168 / 1000000000000), orderedInterval (36731155105 / 1000000000000) (36731163163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1361391934748841 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41679890278 / 1000000000000) (41679894916 / 1000000000000), orderedInterval (-11605993807 / 1000000000000) (-11605989169 / 1000000000000)))) (orderedInterval (8037764551 / 1000000000000) (8037766469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1134986662949529 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46250987776 / 1000000000000) (46250989680 / 1000000000000), orderedInterval (-10302223023 / 1000000000000) (-10302221119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1002795137408109 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7842861895 / 1000000000000) (7842861896 / 1000000000000), orderedInterval (49762621319 / 1000000000000) (49762621320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (290649116638791 / 800000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13497051465 / 1000000000000) (-13497051341 / 1000000000000), orderedInterval (39643077825 / 1000000000000) (39643077949 / 1000000000000)))) (orderedInterval (808060177 / 1000000000000) (808060275 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks2_2 :
    compactCertificate324.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (803950752647877 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36708063842 / 1000000000000) (36708063843 / 1000000000000), orderedInterval (42569859000 / 1000000000000) (42569859001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (681517956530397 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61041942786 / 1000000000000) (61041942811 / 1000000000000), orderedInterval (3037464538 / 1000000000000) (3037464563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (426462293303391 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42711855657 / 1000000000000) (42711855658 / 1000000000000), orderedInterval (64196074486 / 1000000000000) (64196074487 / 1000000000000)))) (orderedInterval (8359059598 / 1000000000000) (8359059643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (229352839688097 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (105368041157 / 1000000000000) (105368041181 / 1000000000000), orderedInterval (-1125741116 / 1000000000000) (-1125741092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (622737575235291 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36666568197 / 1000000000000) (-36666556836 / 1000000000000), orderedInterval (52508011137 / 1000000000000) (52508022498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (850294919510907 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14584204773 / 1000000000000) (-14584204615 / 1000000000000), orderedInterval (52780172999 / 1000000000000) (52780173157 / 1000000000000)))) (orderedInterval (-1637518282 / 1000000000000) (-1637518083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (359537706696609 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35674931357 / 1000000000000) (35674933988 / 1000000000000), orderedInterval (-76421915161 / 1000000000000) (-76421912530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1461500816785089 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41176741014 / 1000000000000) (41176742685 / 1000000000000), orderedInterval (-6900840567 / 1000000000000) (-6900838896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (976214813725551 / 4000000000000) 2 (IntervalRat.scale (393 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10428796837 / 1000000000000) (-10428796786 / 1000000000000), orderedInterval (50019050782 / 1000000000000) (50019050833 / 1000000000000)))) (orderedInterval (8580505852 / 1000000000000) (8580506455 / 1000000000000))) = true
  rfl'

theorem compactCertificate324_chunkChecks2 :
    compactCertificate324.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate324.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate324_chunkChecks2_0
    compactCertificate324_chunkChecks2_1 compactCertificate324_chunkChecks2_2

theorem compactCertificate324_chunkChecks3_0 :
    compactCertificate324.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (393 / 2) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33789477912 / 1000000000000) (33789489777 / 1000000000000), orderedInterval (-45890668186 / 1000000000000) (-45890656321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (578964042525093 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56242073694 / 1000000000000) (56242073695 / 1000000000000), orderedInterval (34950486996 / 1000000000000) (34950486997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (187225075785669 / 800000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37531795668 / 1000000000000) (37531843171 / 1000000000000), orderedInterval (-36296160036 / 1000000000000) (-36296112534 / 1000000000000)))) (orderedInterval (21741999668 / 1000000000000) (21742009144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (168940263651951 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100907478921 / 1000000000000) (-100907449622 / 1000000000000), orderedInterval (71126981148 / 1000000000000) (71127010448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (453797311582947 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67948732399 / 1000000000000) (67948732400 / 1000000000000), orderedInterval (31235037328 / 1000000000000) (31235037329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1232147977096599 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36870072134 / 1000000000000) (36870072135 / 1000000000000), orderedInterval (26535190477 / 1000000000000) (26535190478 / 1000000000000)))) (orderedInterval (7026647834 / 1000000000000) (7026647894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (907594623166287 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52791391343 / 1000000000000) (52791391368 / 1000000000000), orderedInterval (4220405596 / 1000000000000) (4220405621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1555178856250251 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (902362829 / 1000000000000) (902362830 / 1000000000000), orderedInterval (40453825504 / 1000000000000) (40453825506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1145537706696609 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45228514352 / 1000000000000) (-45228514350 / 1000000000000), orderedInterval (-13237713767 / 1000000000000) (-13237713765 / 1000000000000)))) (orderedInterval (10642927808 / 1000000000000) (10642927871 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate324_chunkChecks3_1 :
    compactCertificate324.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1757549430314607 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13034225099 / 1000000000000) (13034225100 / 1000000000000), orderedInterval (35748140074 / 1000000000000) (35748140075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1014721636706103 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (184868067 / 1000000000000) (184868070 / 1000000000000), orderedInterval (-50095327495 / 1000000000000) (-50095327493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1800641350998627 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-37303480438 / 1000000000000) (-37303478666 / 1000000000000), orderedInterval (4801294116 / 1000000000000) (4801295888 / 1000000000000)))) (orderedInterval (70596404066 / 1000000000000) (70596407863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1682392723155663 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15503149185 / 1000000000000) (15503149186 / 1000000000000), orderedInterval (35664321164 / 1000000000000) (35664321165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1200634832078079 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27841906226 / 1000000000000) (-27841898168 / 1000000000000), orderedInterval (36731155105 / 1000000000000) (36731163163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1361391934748841 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41679890278 / 1000000000000) (41679894916 / 1000000000000), orderedInterval (-11605993807 / 1000000000000) (-11605989169 / 1000000000000)))) (orderedInterval (-6412049253 / 1000000000000) (-6412046298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1134986662949529 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46250987776 / 1000000000000) (46250989680 / 1000000000000), orderedInterval (-10302223023 / 1000000000000) (-10302221119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1002795137408109 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7842861895 / 1000000000000) (7842861896 / 1000000000000), orderedInterval (49762621319 / 1000000000000) (49762621320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (290649116638791 / 800000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13497051465 / 1000000000000) (-13497051341 / 1000000000000), orderedInterval (39643077825 / 1000000000000) (39643077949 / 1000000000000)))) (orderedInterval (-147501902 / 1000000000000) (-147501752 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate324_chunkChecks3_2 :
    compactCertificate324.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (803950752647877 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36708063842 / 1000000000000) (36708063843 / 1000000000000), orderedInterval (42569859000 / 1000000000000) (42569859001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (681517956530397 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61041942786 / 1000000000000) (61041942811 / 1000000000000), orderedInterval (3037464538 / 1000000000000) (3037464563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (426462293303391 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42711855657 / 1000000000000) (42711855658 / 1000000000000), orderedInterval (64196074486 / 1000000000000) (64196074487 / 1000000000000)))) (orderedInterval (7019242211 / 1000000000000) (7019242255 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (229352839688097 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (105368041157 / 1000000000000) (105368041181 / 1000000000000), orderedInterval (-1125741116 / 1000000000000) (-1125741092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (622737575235291 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36666568197 / 1000000000000) (-36666556836 / 1000000000000), orderedInterval (52508011137 / 1000000000000) (52508022498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (850294919510907 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14584204773 / 1000000000000) (-14584204615 / 1000000000000), orderedInterval (52780172999 / 1000000000000) (52780173157 / 1000000000000)))) (orderedInterval (5721197294 / 1000000000000) (5721197461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (359537706696609 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35674931357 / 1000000000000) (35674933988 / 1000000000000), orderedInterval (-76421915161 / 1000000000000) (-76421912530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1461500816785089 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41176741014 / 1000000000000) (41176742685 / 1000000000000), orderedInterval (-6900840567 / 1000000000000) (-6900838896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (976214813725551 / 4000000000000) 3 (IntervalRat.scale (393 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10428796837 / 1000000000000) (-10428796786 / 1000000000000), orderedInterval (50019050782 / 1000000000000) (50019050833 / 1000000000000)))) (orderedInterval (14369185163 / 1000000000000) (14369186234 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate324_chunkChecks3 :
    compactCertificate324.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate324.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate324_chunkChecks3_0
    compactCertificate324_chunkChecks3_1 compactCertificate324_chunkChecks3_2

theorem compactCertificate324_chunkChecks4_0 :
    compactCertificate324.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (393 / 2) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33789477912 / 1000000000000) (33789489777 / 1000000000000), orderedInterval (-45890668186 / 1000000000000) (-45890656321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (578964042525093 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56242073694 / 1000000000000) (56242073695 / 1000000000000), orderedInterval (34950486996 / 1000000000000) (34950486997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (187225075785669 / 800000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37531795668 / 1000000000000) (37531843171 / 1000000000000), orderedInterval (-36296160036 / 1000000000000) (-36296112534 / 1000000000000)))) (orderedInterval (17756950200 / 1000000000000) (17756960632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (168940263651951 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100907478921 / 1000000000000) (-100907449622 / 1000000000000), orderedInterval (71126981148 / 1000000000000) (71127010448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (453797311582947 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67948732399 / 1000000000000) (67948732400 / 1000000000000), orderedInterval (31235037328 / 1000000000000) (31235037329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1232147977096599 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36870072134 / 1000000000000) (36870072135 / 1000000000000), orderedInterval (26535190477 / 1000000000000) (26535190478 / 1000000000000)))) (orderedInterval (-15621945258 / 1000000000000) (-15621945171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (907594623166287 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52791391343 / 1000000000000) (52791391368 / 1000000000000), orderedInterval (4220405596 / 1000000000000) (4220405621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1555178856250251 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (902362829 / 1000000000000) (902362830 / 1000000000000), orderedInterval (40453825504 / 1000000000000) (40453825506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1145537706696609 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-45228514352 / 1000000000000) (-45228514350 / 1000000000000), orderedInterval (-13237713767 / 1000000000000) (-13237713765 / 1000000000000)))) (orderedInterval (-5466572379 / 1000000000000) (-5466572263 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate324_chunkChecks4_1 :
    compactCertificate324.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1757549430314607 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13034225099 / 1000000000000) (13034225100 / 1000000000000), orderedInterval (35748140074 / 1000000000000) (35748140075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1014721636706103 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (184868067 / 1000000000000) (184868070 / 1000000000000), orderedInterval (-50095327495 / 1000000000000) (-50095327493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1800641350998627 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-37303480438 / 1000000000000) (-37303478666 / 1000000000000), orderedInterval (4801294116 / 1000000000000) (4801295888 / 1000000000000)))) (orderedInterval (-204640620736 / 1000000000000) (-204640612078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1682392723155663 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15503149185 / 1000000000000) (15503149186 / 1000000000000), orderedInterval (35664321164 / 1000000000000) (35664321165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1200634832078079 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27841906226 / 1000000000000) (-27841898168 / 1000000000000), orderedInterval (36731155105 / 1000000000000) (36731163163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1361391934748841 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41679890278 / 1000000000000) (41679894916 / 1000000000000), orderedInterval (-11605993807 / 1000000000000) (-11605989169 / 1000000000000)))) (orderedInterval (-22041806563 / 1000000000000) (-22041801988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1134986662949529 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (46250987776 / 1000000000000) (46250989680 / 1000000000000), orderedInterval (-10302223023 / 1000000000000) (-10302221119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1002795137408109 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7842861895 / 1000000000000) (7842861896 / 1000000000000), orderedInterval (49762621319 / 1000000000000) (49762621320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (290649116638791 / 800000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13497051465 / 1000000000000) (-13497051341 / 1000000000000), orderedInterval (39643077825 / 1000000000000) (39643077949 / 1000000000000)))) (orderedInterval (-2903897576 / 1000000000000) (-2903897343 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate324_chunkChecks4_2 :
    compactCertificate324.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (803950752647877 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36708063842 / 1000000000000) (36708063843 / 1000000000000), orderedInterval (42569859000 / 1000000000000) (42569859001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (681517956530397 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61041942786 / 1000000000000) (61041942811 / 1000000000000), orderedInterval (3037464538 / 1000000000000) (3037464563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (426462293303391 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42711855657 / 1000000000000) (42711855658 / 1000000000000), orderedInterval (64196074486 / 1000000000000) (64196074487 / 1000000000000)))) (orderedInterval (-8327716715 / 1000000000000) (-8327716672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (229352839688097 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (105368041157 / 1000000000000) (105368041181 / 1000000000000), orderedInterval (-1125741116 / 1000000000000) (-1125741092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (622737575235291 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36666568197 / 1000000000000) (-36666556836 / 1000000000000), orderedInterval (52508011137 / 1000000000000) (52508022498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (850294919510907 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14584204773 / 1000000000000) (-14584204615 / 1000000000000), orderedInterval (52780172999 / 1000000000000) (52780173157 / 1000000000000)))) (orderedInterval (1786201351 / 1000000000000) (1786201494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (359537706696609 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35674931357 / 1000000000000) (35674933988 / 1000000000000), orderedInterval (-76421915161 / 1000000000000) (-76421912530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1461500816785089 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (41176741014 / 1000000000000) (41176742685 / 1000000000000), orderedInterval (-6900840567 / 1000000000000) (-6900838896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (976214813725551 / 4000000000000) 4 (IntervalRat.scale (393 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10428796837 / 1000000000000) (-10428796786 / 1000000000000), orderedInterval (50019050782 / 1000000000000) (50019050833 / 1000000000000)))) (orderedInterval (-35548010342 / 1000000000000) (-35548008403 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate324_chunkChecks4 :
    compactCertificate324.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate324.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate324_chunkChecks4_0
    compactCertificate324_chunkChecks4_1 compactCertificate324_chunkChecks4_2

theorem compactCertificate324_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate324.chunkCheck r b = true :=
  compactCertificate324.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate324_chunkChecks0
    · exact compactCertificate324_chunkChecks1
    · exact compactCertificate324_chunkChecks2
    · exact compactCertificate324_chunkChecks3
    · exact compactCertificate324_chunkChecks4)

theorem compactCertificate324_coefficient0 :
    compactCertificate324.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate324_coefficient1 :
    compactCertificate324.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate324_coefficient2 :
    compactCertificate324.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate324_coefficient3 :
    compactCertificate324.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate324_coefficient4 :
    compactCertificate324.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate324_coefficients : ∀ r : Fin 5,
    compactCertificate324.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate324_coefficient0
  · exact compactCertificate324_coefficient1
  · exact compactCertificate324_coefficient2
  · exact compactCertificate324_coefficient3
  · exact compactCertificate324_coefficient4

theorem compactCertificate324_lower : (1 : ℚ) ≤ compactCertificate324.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate324, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate324_proves {t : ℝ} (ht : t ∈ compactCertificate324.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate324.proves compactCertificate324_states compactCertificate324_chunks
    compactCertificate324_coefficients compactCertificate324_lower ht

end Erdos232
