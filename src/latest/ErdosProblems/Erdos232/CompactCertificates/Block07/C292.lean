/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate292 : CompactCertificate where
  left := 166
  right := 333 / 2
  center := 665 / 4
  grid := fun i =>
    match i.val with
    | 0 => 53
    | 1 => 39
    | 2 => 63
    | 3 => 11
    | 4 => 31
    | 5 => 83
    | 6 => 61
    | 7 => 105
    | 8 => 77
    | 9 => 118
    | 10 => 68
    | 11 => 121
    | 12 => 113
    | 13 => 81
    | 14 => 92
    | 15 => 76
    | 16 => 68
    | 17 => 98
    | 18 => 54
    | 19 => 46
    | 20 => 29
    | 21 => 15
    | 22 => 42
    | 23 => 57
    | 24 => 24
    | 25 => 98
    | _ => 66
  point := fun i =>
    match i.val with
    | 0 => 665 / 4
    | 1 => 195934396070833 / 1600000000000
    | 2 => 63361157963089 / 320000000000
    | 3 => 57173168106131 / 1600000000000
    | 4 => 153575171604407 / 1600000000000
    | 5 => 416986465531419 / 1600000000000
    | 6 => 307150343208947 / 1600000000000
    | 7 => 526307348298431 / 1600000000000
    | 8 => 387675610663229 / 1600000000000
    | 9 => 594794082014867 / 1600000000000
    | 10 => 343404523363643 / 1600000000000
    | 11 => 609377352882487 / 1600000000000
    | 12 => 569359369414003 / 1600000000000
    | 13 => 406321711619299 / 1600000000000
    | 14 => 460725514813221 / 1600000000000
    | 15 => 384104901201749 / 1600000000000
    | 16 => 339368328944729 / 1600000000000
    | 17 => 98362169244171 / 320000000000
    | 18 => 272074936646737 / 1600000000000
    | 19 => 230640936942857 / 1600000000000
    | 20 => 144324389336771 / 1600000000000
    | 21 => 77618136586557 / 1600000000000
    | 22 => 210748339710671 / 1600000000000
    | 23 => 287758840445167 / 1600000000000
    | 24 => 121675610663229 / 1600000000000
    | 25 => 494604602118109 / 1600000000000
    | _ => 330372952227731 / 1600000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-31295556858 / 1000000000000) (-31295556857 / 1000000000000), orderedInterval (-53290225306 / 1000000000000) (-53290225305 / 1000000000000))
    | 1 => (orderedInterval (-47610814250 / 1000000000000) (-47610814249 / 1000000000000), orderedInterval (-53952187771 / 1000000000000) (-53952187770 / 1000000000000))
    | 2 => (orderedInterval (-43267979161 / 1000000000000) (-43267979160 / 1000000000000), orderedInterval (-36538699240 / 1000000000000) (-36538699239 / 1000000000000))
    | 3 => (orderedInterval (-123608280746 / 1000000000000) (-123608277552 / 1000000000000), orderedInterval (52084502869 / 1000000000000) (52084506063 / 1000000000000))
    | 4 => (orderedInterval (47371985306 / 1000000000000) (47372002061 / 1000000000000), orderedInterval (-66492157426 / 1000000000000) (-66492140671 / 1000000000000))
    | 5 => (orderedInterval (-29882026741 / 1000000000000) (-29882026740 / 1000000000000), orderedInterval (-39310306714 / 1000000000000) (-39310306713 / 1000000000000))
    | 6 => (orderedInterval (-51747384392 / 1000000000000) (-51747384391 / 1000000000000), orderedInterval (-25133091699 / 1000000000000) (-25133091698 / 1000000000000))
    | 7 => (orderedInterval (6144001626 / 1000000000000) (6144001636 / 1000000000000), orderedInterval (-43570887888 / 1000000000000) (-43570887878 / 1000000000000))
    | 8 => (orderedInterval (-47384179502 / 1000000000000) (-47384179501 / 1000000000000), orderedInterval (-19451347679 / 1000000000000) (-19451347678 / 1000000000000))
    | 9 => (orderedInterval (40068895117 / 1000000000000) (40068899673 / 1000000000000), orderedInterval (-10397660336 / 1000000000000) (-10397655780 / 1000000000000))
    | 10 => (orderedInterval (53225276857 / 1000000000000) (53225278074 / 1000000000000), orderedInterval (-11666057946 / 1000000000000) (-11666056729 / 1000000000000))
    | 11 => (orderedInterval (-40816529288 / 1000000000000) (-40816529177 / 1000000000000), orderedInterval (-2299721441 / 1000000000000) (-2299721330 / 1000000000000))
    | 12 => (orderedInterval (-42210424089 / 1000000000000) (-42210423619 / 1000000000000), orderedInterval (2759666715 / 1000000000000) (2759667185 / 1000000000000))
    | 13 => (orderedInterval (-13208608731 / 1000000000000) (-13208608730 / 1000000000000), orderedInterval (-48268888166 / 1000000000000) (-48268888165 / 1000000000000))
    | 14 => (orderedInterval (-13360317619 / 1000000000000) (-13360317499 / 1000000000000), orderedInterval (45104762448 / 1000000000000) (45104762569 / 1000000000000))
    | 15 => (orderedInterval (44725028187 / 1000000000000) (44725060442 / 1000000000000), orderedInterval (-25618162128 / 1000000000000) (-25618129874 / 1000000000000))
    | 16 => (orderedInterval (-36871660936 / 1000000000000) (-36871631710 / 1000000000000), orderedInterval (40607470593 / 1000000000000) (40607499820 / 1000000000000))
    | 17 => (orderedInterval (13043604387 / 1000000000000) (13043604388 / 1000000000000), orderedInterval (43578910443 / 1000000000000) (43578910444 / 1000000000000))
    | 18 => (orderedInterval (56700530041 / 1000000000000) (56700530043 / 1000000000000), orderedInterval (22829564480 / 1000000000000) (22829564481 / 1000000000000))
    | 19 => (orderedInterval (27210388639 / 1000000000000) (27210388640 / 1000000000000), orderedInterval (60535353958 / 1000000000000) (60535353959 / 1000000000000))
    | 20 => (orderedInterval (10009478886 / 1000000000000) (10009478931 / 1000000000000), orderedInterval (-83467530322 / 1000000000000) (-83467530277 / 1000000000000))
    | 21 => (orderedInterval (-94578969736 / 1000000000000) (-94578941424 / 1000000000000), orderedInterval (65609682048 / 1000000000000) (65609710359 / 1000000000000))
    | 22 => (orderedInterval (36649614156 / 1000000000000) (36649614157 / 1000000000000), orderedInterval (58937392830 / 1000000000000) (58937392831 / 1000000000000))
    | 23 => (orderedInterval (-59493885971 / 1000000000000) (-59493885918 / 1000000000000), orderedInterval (-286715725 / 1000000000000) (-286715672 / 1000000000000))
    | 24 => (orderedInterval (90624269894 / 1000000000000) (90624269897 / 1000000000000), orderedInterval (11991412082 / 1000000000000) (11991412086 / 1000000000000))
    | 25 => (orderedInterval (40541945109 / 1000000000000) (40541972531 / 1000000000000), orderedInterval (-20455630329 / 1000000000000) (-20455602907 / 1000000000000))
    | _ => (orderedInterval (-4283864125 / 1000000000000) (-4283864115 / 1000000000000), orderedInterval (55371138368 / 1000000000000) (55371138378 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15387117948 / 1000000000000) (-15387117935 / 1000000000000)
      | 1 => orderedInterval (5194998611 / 1000000000000) (5194999278 / 1000000000000)
      | 2 => orderedInterval (-1334687727 / 1000000000000) (-1334687717 / 1000000000000)
      | 3 => orderedInterval (-8978514818 / 1000000000000) (-8978513836 / 1000000000000)
      | 4 => orderedInterval (-419404598 / 1000000000000) (-419404568 / 1000000000000)
      | 5 => orderedInterval (2960478611 / 1000000000000) (2960480672 / 1000000000000)
      | 6 => orderedInterval (-10280231735 / 1000000000000) (-10280231690 / 1000000000000)
      | 7 => orderedInterval (5474490659 / 1000000000000) (5474491206 / 1000000000000)
      | _ => orderedInterval (-1950109261 / 1000000000000) (-1950106980 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-24046348369 / 1000000000000) (-24046348355 / 1000000000000)
      | 1 => orderedInterval (2857680923 / 1000000000000) (2857681307 / 1000000000000)
      | 2 => orderedInterval (1973902770 / 1000000000000) (1973902788 / 1000000000000)
      | 3 => orderedInterval (2266401600 / 1000000000000) (2266403700 / 1000000000000)
      | 4 => orderedInterval (-7474293384 / 1000000000000) (-7474293332 / 1000000000000)
      | 5 => orderedInterval (-1328970437 / 1000000000000) (-1328967741 / 1000000000000)
      | 6 => orderedInterval (-8178822513 / 1000000000000) (-8178822472 / 1000000000000)
      | 7 => orderedInterval (-1389109549 / 1000000000000) (-1389109373 / 1000000000000)
      | _ => orderedInterval (-9774070946 / 1000000000000) (-9774066727 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16391348949 / 1000000000000) (16391348965 / 1000000000000)
      | 1 => orderedInterval (-5876006708 / 1000000000000) (-5876006468 / 1000000000000)
      | 2 => orderedInterval (3162487885 / 1000000000000) (3162487915 / 1000000000000)
      | 3 => orderedInterval (59464181537 / 1000000000000) (59464186123 / 1000000000000)
      | 4 => orderedInterval (-734687921 / 1000000000000) (-734687826 / 1000000000000)
      | 5 => orderedInterval (-5645139698 / 1000000000000) (-5645136148 / 1000000000000)
      | 6 => orderedInterval (10595953363 / 1000000000000) (10595953401 / 1000000000000)
      | 7 => orderedInterval (-4954414244 / 1000000000000) (-4954414175 / 1000000000000)
      | _ => orderedInterval (10114766421 / 1000000000000) (10114774263 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (24846148086 / 1000000000000) (24846148104 / 1000000000000)
      | 1 => orderedInterval (-10257209613 / 1000000000000) (-10257209445 / 1000000000000)
      | 2 => orderedInterval (-8973409836 / 1000000000000) (-8973409780 / 1000000000000)
      | 3 => orderedInterval (-15223347238 / 1000000000000) (-15223337136 / 1000000000000)
      | 4 => orderedInterval (17947476671 / 1000000000000) (17947476849 / 1000000000000)
      | 5 => orderedInterval (-1301847159 / 1000000000000) (-1301842489 / 1000000000000)
      | 6 => orderedInterval (6509636512 / 1000000000000) (6509636549 / 1000000000000)
      | 7 => orderedInterval (697018231 / 1000000000000) (697018269 / 1000000000000)
      | _ => orderedInterval (9131411438 / 1000000000000) (9131425986 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17942074786 / 1000000000000) (-17942074764 / 1000000000000)
      | 1 => orderedInterval (13146778066 / 1000000000000) (13146778209 / 1000000000000)
      | 2 => orderedInterval (-7963117177 / 1000000000000) (-7963117074 / 1000000000000)
      | 3 => orderedInterval (-326670154105 / 1000000000000) (-326670131643 / 1000000000000)
      | 4 => orderedInterval (9587443967 / 1000000000000) (9587444309 / 1000000000000)
      | 5 => orderedInterval (11754215626 / 1000000000000) (11754221816 / 1000000000000)
      | 6 => orderedInterval (-10843180747 / 1000000000000) (-10843180711 / 1000000000000)
      | 7 => orderedInterval (5921145606 / 1000000000000) (5921145636 / 1000000000000)
      | _ => orderedInterval (-37622779879 / 1000000000000) (-37622752782 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-24720098206 / 1000000000000) (-24720091570 / 1000000000000)
    | 1 => orderedInterval (-45093629905 / 1000000000000) (-45093620205 / 1000000000000)
    | 2 => orderedInterval (82518489584 / 1000000000000) (82518506050 / 1000000000000)
    | 3 => orderedInterval (23375877092 / 1000000000000) (23375906907 / 1000000000000)
    | _ => orderedInterval (-360631723429 / 1000000000000) (-360631667004 / 1000000000000)

theorem compactCertificate292_stateChecks0 :
    compactCertificate292.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (665 / 4)) (orderedInterval (-31295556858 / 1000000000000) (-31295556857 / 1000000000000), orderedInterval (-53290225306 / 1000000000000) (-53290225305 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (195934396070833 / 1600000000000)) (orderedInterval (-47610814250 / 1000000000000) (-47610814249 / 1000000000000), orderedInterval (-53952187771 / 1000000000000) (-53952187770 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (63361157963089 / 320000000000)) (orderedInterval (-43267979161 / 1000000000000) (-43267979160 / 1000000000000), orderedInterval (-36538699240 / 1000000000000) (-36538699239 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_stateChecks1 :
    compactCertificate292.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (57173168106131 / 1600000000000)) (orderedInterval (-123608280746 / 1000000000000) (-123608277552 / 1000000000000), orderedInterval (52084502869 / 1000000000000) (52084506063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (153575171604407 / 1600000000000)) (orderedInterval (47371985306 / 1000000000000) (47372002061 / 1000000000000), orderedInterval (-66492157426 / 1000000000000) (-66492140671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (416986465531419 / 1600000000000)) (orderedInterval (-29882026741 / 1000000000000) (-29882026740 / 1000000000000), orderedInterval (-39310306714 / 1000000000000) (-39310306713 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_stateChecks2 :
    compactCertificate292.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (307150343208947 / 1600000000000)) (orderedInterval (-51747384392 / 1000000000000) (-51747384391 / 1000000000000), orderedInterval (-25133091699 / 1000000000000) (-25133091698 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (526307348298431 / 1600000000000)) (orderedInterval (6144001626 / 1000000000000) (6144001636 / 1000000000000), orderedInterval (-43570887888 / 1000000000000) (-43570887878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (387675610663229 / 1600000000000)) (orderedInterval (-47384179502 / 1000000000000) (-47384179501 / 1000000000000), orderedInterval (-19451347679 / 1000000000000) (-19451347678 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_stateChecks3 :
    compactCertificate292.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (594794082014867 / 1600000000000)) (orderedInterval (40068895117 / 1000000000000) (40068899673 / 1000000000000), orderedInterval (-10397660336 / 1000000000000) (-10397655780 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (343404523363643 / 1600000000000)) (orderedInterval (53225276857 / 1000000000000) (53225278074 / 1000000000000), orderedInterval (-11666057946 / 1000000000000) (-11666056729 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (609377352882487 / 1600000000000)) (orderedInterval (-40816529288 / 1000000000000) (-40816529177 / 1000000000000), orderedInterval (-2299721441 / 1000000000000) (-2299721330 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_stateChecks4 :
    compactCertificate292.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (569359369414003 / 1600000000000)) (orderedInterval (-42210424089 / 1000000000000) (-42210423619 / 1000000000000), orderedInterval (2759666715 / 1000000000000) (2759667185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (406321711619299 / 1600000000000)) (orderedInterval (-13208608731 / 1000000000000) (-13208608730 / 1000000000000), orderedInterval (-48268888166 / 1000000000000) (-48268888165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (460725514813221 / 1600000000000)) (orderedInterval (-13360317619 / 1000000000000) (-13360317499 / 1000000000000), orderedInterval (45104762448 / 1000000000000) (45104762569 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_stateChecks5 :
    compactCertificate292.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (384104901201749 / 1600000000000)) (orderedInterval (44725028187 / 1000000000000) (44725060442 / 1000000000000), orderedInterval (-25618162128 / 1000000000000) (-25618129874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (339368328944729 / 1600000000000)) (orderedInterval (-36871660936 / 1000000000000) (-36871631710 / 1000000000000), orderedInterval (40607470593 / 1000000000000) (40607499820 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (98362169244171 / 320000000000)) (orderedInterval (13043604387 / 1000000000000) (13043604388 / 1000000000000), orderedInterval (43578910443 / 1000000000000) (43578910444 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_stateChecks6 :
    compactCertificate292.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (272074936646737 / 1600000000000)) (orderedInterval (56700530041 / 1000000000000) (56700530043 / 1000000000000), orderedInterval (22829564480 / 1000000000000) (22829564481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (230640936942857 / 1600000000000)) (orderedInterval (27210388639 / 1000000000000) (27210388640 / 1000000000000), orderedInterval (60535353958 / 1000000000000) (60535353959 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (144324389336771 / 1600000000000)) (orderedInterval (10009478886 / 1000000000000) (10009478931 / 1000000000000), orderedInterval (-83467530322 / 1000000000000) (-83467530277 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_stateChecks7 :
    compactCertificate292.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (77618136586557 / 1600000000000)) (orderedInterval (-94578969736 / 1000000000000) (-94578941424 / 1000000000000), orderedInterval (65609682048 / 1000000000000) (65609710359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (210748339710671 / 1600000000000)) (orderedInterval (36649614156 / 1000000000000) (36649614157 / 1000000000000), orderedInterval (58937392830 / 1000000000000) (58937392831 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (287758840445167 / 1600000000000)) (orderedInterval (-59493885971 / 1000000000000) (-59493885918 / 1000000000000), orderedInterval (-286715725 / 1000000000000) (-286715672 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_stateChecks8 :
    compactCertificate292.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (121675610663229 / 1600000000000)) (orderedInterval (90624269894 / 1000000000000) (90624269897 / 1000000000000), orderedInterval (11991412082 / 1000000000000) (11991412086 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (494604602118109 / 1600000000000)) (orderedInterval (40541945109 / 1000000000000) (40541972531 / 1000000000000), orderedInterval (-20455630329 / 1000000000000) (-20455602907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (330372952227731 / 1600000000000)) (orderedInterval (-4283864125 / 1000000000000) (-4283864115 / 1000000000000), orderedInterval (55371138368 / 1000000000000) (55371138378 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_states : ∀ j,
    BesselStateValid (compactCertificate292.point j) (compactCertificate292.state j) :=
  compactCertificate292.statesValid_of_checks3 compactCertificate292_stateChecks0
    compactCertificate292_stateChecks1 compactCertificate292_stateChecks2
    compactCertificate292_stateChecks3 compactCertificate292_stateChecks4
    compactCertificate292_stateChecks5 compactCertificate292_stateChecks6
    compactCertificate292_stateChecks7 compactCertificate292_stateChecks8

theorem compactCertificate292_chunkChecks0_0 :
    compactCertificate292.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (665 / 4) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31295556858 / 1000000000000) (-31295556857 / 1000000000000), orderedInterval (-53290225306 / 1000000000000) (-53290225305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (195934396070833 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47610814250 / 1000000000000) (-47610814249 / 1000000000000), orderedInterval (-53952187771 / 1000000000000) (-53952187770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (63361157963089 / 320000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43267979161 / 1000000000000) (-43267979160 / 1000000000000), orderedInterval (-36538699240 / 1000000000000) (-36538699239 / 1000000000000)))) (orderedInterval (-15387117948 / 1000000000000) (-15387117935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (57173168106131 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123608280746 / 1000000000000) (-123608277552 / 1000000000000), orderedInterval (52084502869 / 1000000000000) (52084506063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (153575171604407 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47371985306 / 1000000000000) (47372002061 / 1000000000000), orderedInterval (-66492157426 / 1000000000000) (-66492140671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (416986465531419 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29882026741 / 1000000000000) (-29882026740 / 1000000000000), orderedInterval (-39310306714 / 1000000000000) (-39310306713 / 1000000000000)))) (orderedInterval (5194998611 / 1000000000000) (5194999278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (307150343208947 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51747384392 / 1000000000000) (-51747384391 / 1000000000000), orderedInterval (-25133091699 / 1000000000000) (-25133091698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (526307348298431 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6144001626 / 1000000000000) (6144001636 / 1000000000000), orderedInterval (-43570887888 / 1000000000000) (-43570887878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (387675610663229 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47384179502 / 1000000000000) (-47384179501 / 1000000000000), orderedInterval (-19451347679 / 1000000000000) (-19451347678 / 1000000000000)))) (orderedInterval (-1334687727 / 1000000000000) (-1334687717 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks0_1 :
    compactCertificate292.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (594794082014867 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (40068895117 / 1000000000000) (40068899673 / 1000000000000), orderedInterval (-10397660336 / 1000000000000) (-10397655780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (343404523363643 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (53225276857 / 1000000000000) (53225278074 / 1000000000000), orderedInterval (-11666057946 / 1000000000000) (-11666056729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (609377352882487 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40816529288 / 1000000000000) (-40816529177 / 1000000000000), orderedInterval (-2299721441 / 1000000000000) (-2299721330 / 1000000000000)))) (orderedInterval (-8978514818 / 1000000000000) (-8978513836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (569359369414003 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42210424089 / 1000000000000) (-42210423619 / 1000000000000), orderedInterval (2759666715 / 1000000000000) (2759667185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (406321711619299 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13208608731 / 1000000000000) (-13208608730 / 1000000000000), orderedInterval (-48268888166 / 1000000000000) (-48268888165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (460725514813221 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13360317619 / 1000000000000) (-13360317499 / 1000000000000), orderedInterval (45104762448 / 1000000000000) (45104762569 / 1000000000000)))) (orderedInterval (-419404598 / 1000000000000) (-419404568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (384104901201749 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44725028187 / 1000000000000) (44725060442 / 1000000000000), orderedInterval (-25618162128 / 1000000000000) (-25618129874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (339368328944729 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36871660936 / 1000000000000) (-36871631710 / 1000000000000), orderedInterval (40607470593 / 1000000000000) (40607499820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (98362169244171 / 320000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13043604387 / 1000000000000) (13043604388 / 1000000000000), orderedInterval (43578910443 / 1000000000000) (43578910444 / 1000000000000)))) (orderedInterval (2960478611 / 1000000000000) (2960480672 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks0_2 :
    compactCertificate292.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (272074936646737 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56700530041 / 1000000000000) (56700530043 / 1000000000000), orderedInterval (22829564480 / 1000000000000) (22829564481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (230640936942857 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27210388639 / 1000000000000) (27210388640 / 1000000000000), orderedInterval (60535353958 / 1000000000000) (60535353959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (144324389336771 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10009478886 / 1000000000000) (10009478931 / 1000000000000), orderedInterval (-83467530322 / 1000000000000) (-83467530277 / 1000000000000)))) (orderedInterval (-10280231735 / 1000000000000) (-10280231690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (77618136586557 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-94578969736 / 1000000000000) (-94578941424 / 1000000000000), orderedInterval (65609682048 / 1000000000000) (65609710359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (210748339710671 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36649614156 / 1000000000000) (36649614157 / 1000000000000), orderedInterval (58937392830 / 1000000000000) (58937392831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (287758840445167 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-59493885971 / 1000000000000) (-59493885918 / 1000000000000), orderedInterval (-286715725 / 1000000000000) (-286715672 / 1000000000000)))) (orderedInterval (5474490659 / 1000000000000) (5474491206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (121675610663229 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90624269894 / 1000000000000) (90624269897 / 1000000000000), orderedInterval (11991412082 / 1000000000000) (11991412086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (494604602118109 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40541945109 / 1000000000000) (40541972531 / 1000000000000), orderedInterval (-20455630329 / 1000000000000) (-20455602907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (330372952227731 / 1600000000000) 0 (IntervalRat.scale (665 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4283864125 / 1000000000000) (-4283864115 / 1000000000000), orderedInterval (55371138368 / 1000000000000) (55371138378 / 1000000000000)))) (orderedInterval (-1950109261 / 1000000000000) (-1950106980 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks0 :
    compactCertificate292.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate292.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate292_chunkChecks0_0
    compactCertificate292_chunkChecks0_1 compactCertificate292_chunkChecks0_2

theorem compactCertificate292_chunkChecks1_0 :
    compactCertificate292.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (665 / 4) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31295556858 / 1000000000000) (-31295556857 / 1000000000000), orderedInterval (-53290225306 / 1000000000000) (-53290225305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (195934396070833 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47610814250 / 1000000000000) (-47610814249 / 1000000000000), orderedInterval (-53952187771 / 1000000000000) (-53952187770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (63361157963089 / 320000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43267979161 / 1000000000000) (-43267979160 / 1000000000000), orderedInterval (-36538699240 / 1000000000000) (-36538699239 / 1000000000000)))) (orderedInterval (-24046348369 / 1000000000000) (-24046348355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (57173168106131 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123608280746 / 1000000000000) (-123608277552 / 1000000000000), orderedInterval (52084502869 / 1000000000000) (52084506063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (153575171604407 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47371985306 / 1000000000000) (47372002061 / 1000000000000), orderedInterval (-66492157426 / 1000000000000) (-66492140671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (416986465531419 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29882026741 / 1000000000000) (-29882026740 / 1000000000000), orderedInterval (-39310306714 / 1000000000000) (-39310306713 / 1000000000000)))) (orderedInterval (2857680923 / 1000000000000) (2857681307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (307150343208947 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51747384392 / 1000000000000) (-51747384391 / 1000000000000), orderedInterval (-25133091699 / 1000000000000) (-25133091698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (526307348298431 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6144001626 / 1000000000000) (6144001636 / 1000000000000), orderedInterval (-43570887888 / 1000000000000) (-43570887878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (387675610663229 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47384179502 / 1000000000000) (-47384179501 / 1000000000000), orderedInterval (-19451347679 / 1000000000000) (-19451347678 / 1000000000000)))) (orderedInterval (1973902770 / 1000000000000) (1973902788 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks1_1 :
    compactCertificate292.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (594794082014867 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (40068895117 / 1000000000000) (40068899673 / 1000000000000), orderedInterval (-10397660336 / 1000000000000) (-10397655780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (343404523363643 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (53225276857 / 1000000000000) (53225278074 / 1000000000000), orderedInterval (-11666057946 / 1000000000000) (-11666056729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (609377352882487 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40816529288 / 1000000000000) (-40816529177 / 1000000000000), orderedInterval (-2299721441 / 1000000000000) (-2299721330 / 1000000000000)))) (orderedInterval (2266401600 / 1000000000000) (2266403700 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (569359369414003 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42210424089 / 1000000000000) (-42210423619 / 1000000000000), orderedInterval (2759666715 / 1000000000000) (2759667185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (406321711619299 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13208608731 / 1000000000000) (-13208608730 / 1000000000000), orderedInterval (-48268888166 / 1000000000000) (-48268888165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (460725514813221 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13360317619 / 1000000000000) (-13360317499 / 1000000000000), orderedInterval (45104762448 / 1000000000000) (45104762569 / 1000000000000)))) (orderedInterval (-7474293384 / 1000000000000) (-7474293332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (384104901201749 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44725028187 / 1000000000000) (44725060442 / 1000000000000), orderedInterval (-25618162128 / 1000000000000) (-25618129874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (339368328944729 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36871660936 / 1000000000000) (-36871631710 / 1000000000000), orderedInterval (40607470593 / 1000000000000) (40607499820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (98362169244171 / 320000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13043604387 / 1000000000000) (13043604388 / 1000000000000), orderedInterval (43578910443 / 1000000000000) (43578910444 / 1000000000000)))) (orderedInterval (-1328970437 / 1000000000000) (-1328967741 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks1_2 :
    compactCertificate292.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (272074936646737 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56700530041 / 1000000000000) (56700530043 / 1000000000000), orderedInterval (22829564480 / 1000000000000) (22829564481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (230640936942857 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27210388639 / 1000000000000) (27210388640 / 1000000000000), orderedInterval (60535353958 / 1000000000000) (60535353959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (144324389336771 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10009478886 / 1000000000000) (10009478931 / 1000000000000), orderedInterval (-83467530322 / 1000000000000) (-83467530277 / 1000000000000)))) (orderedInterval (-8178822513 / 1000000000000) (-8178822472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (77618136586557 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-94578969736 / 1000000000000) (-94578941424 / 1000000000000), orderedInterval (65609682048 / 1000000000000) (65609710359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (210748339710671 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36649614156 / 1000000000000) (36649614157 / 1000000000000), orderedInterval (58937392830 / 1000000000000) (58937392831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (287758840445167 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-59493885971 / 1000000000000) (-59493885918 / 1000000000000), orderedInterval (-286715725 / 1000000000000) (-286715672 / 1000000000000)))) (orderedInterval (-1389109549 / 1000000000000) (-1389109373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (121675610663229 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90624269894 / 1000000000000) (90624269897 / 1000000000000), orderedInterval (11991412082 / 1000000000000) (11991412086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (494604602118109 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40541945109 / 1000000000000) (40541972531 / 1000000000000), orderedInterval (-20455630329 / 1000000000000) (-20455602907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (330372952227731 / 1600000000000) 1 (IntervalRat.scale (665 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4283864125 / 1000000000000) (-4283864115 / 1000000000000), orderedInterval (55371138368 / 1000000000000) (55371138378 / 1000000000000)))) (orderedInterval (-9774070946 / 1000000000000) (-9774066727 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks1 :
    compactCertificate292.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate292.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate292_chunkChecks1_0
    compactCertificate292_chunkChecks1_1 compactCertificate292_chunkChecks1_2

theorem compactCertificate292_chunkChecks2_0 :
    compactCertificate292.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (665 / 4) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31295556858 / 1000000000000) (-31295556857 / 1000000000000), orderedInterval (-53290225306 / 1000000000000) (-53290225305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (195934396070833 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47610814250 / 1000000000000) (-47610814249 / 1000000000000), orderedInterval (-53952187771 / 1000000000000) (-53952187770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (63361157963089 / 320000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43267979161 / 1000000000000) (-43267979160 / 1000000000000), orderedInterval (-36538699240 / 1000000000000) (-36538699239 / 1000000000000)))) (orderedInterval (16391348949 / 1000000000000) (16391348965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (57173168106131 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123608280746 / 1000000000000) (-123608277552 / 1000000000000), orderedInterval (52084502869 / 1000000000000) (52084506063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (153575171604407 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47371985306 / 1000000000000) (47372002061 / 1000000000000), orderedInterval (-66492157426 / 1000000000000) (-66492140671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (416986465531419 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29882026741 / 1000000000000) (-29882026740 / 1000000000000), orderedInterval (-39310306714 / 1000000000000) (-39310306713 / 1000000000000)))) (orderedInterval (-5876006708 / 1000000000000) (-5876006468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (307150343208947 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51747384392 / 1000000000000) (-51747384391 / 1000000000000), orderedInterval (-25133091699 / 1000000000000) (-25133091698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (526307348298431 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6144001626 / 1000000000000) (6144001636 / 1000000000000), orderedInterval (-43570887888 / 1000000000000) (-43570887878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (387675610663229 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47384179502 / 1000000000000) (-47384179501 / 1000000000000), orderedInterval (-19451347679 / 1000000000000) (-19451347678 / 1000000000000)))) (orderedInterval (3162487885 / 1000000000000) (3162487915 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks2_1 :
    compactCertificate292.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (594794082014867 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (40068895117 / 1000000000000) (40068899673 / 1000000000000), orderedInterval (-10397660336 / 1000000000000) (-10397655780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (343404523363643 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (53225276857 / 1000000000000) (53225278074 / 1000000000000), orderedInterval (-11666057946 / 1000000000000) (-11666056729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (609377352882487 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40816529288 / 1000000000000) (-40816529177 / 1000000000000), orderedInterval (-2299721441 / 1000000000000) (-2299721330 / 1000000000000)))) (orderedInterval (59464181537 / 1000000000000) (59464186123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (569359369414003 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42210424089 / 1000000000000) (-42210423619 / 1000000000000), orderedInterval (2759666715 / 1000000000000) (2759667185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (406321711619299 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13208608731 / 1000000000000) (-13208608730 / 1000000000000), orderedInterval (-48268888166 / 1000000000000) (-48268888165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (460725514813221 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13360317619 / 1000000000000) (-13360317499 / 1000000000000), orderedInterval (45104762448 / 1000000000000) (45104762569 / 1000000000000)))) (orderedInterval (-734687921 / 1000000000000) (-734687826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (384104901201749 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44725028187 / 1000000000000) (44725060442 / 1000000000000), orderedInterval (-25618162128 / 1000000000000) (-25618129874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (339368328944729 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36871660936 / 1000000000000) (-36871631710 / 1000000000000), orderedInterval (40607470593 / 1000000000000) (40607499820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (98362169244171 / 320000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13043604387 / 1000000000000) (13043604388 / 1000000000000), orderedInterval (43578910443 / 1000000000000) (43578910444 / 1000000000000)))) (orderedInterval (-5645139698 / 1000000000000) (-5645136148 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks2_2 :
    compactCertificate292.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (272074936646737 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56700530041 / 1000000000000) (56700530043 / 1000000000000), orderedInterval (22829564480 / 1000000000000) (22829564481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (230640936942857 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27210388639 / 1000000000000) (27210388640 / 1000000000000), orderedInterval (60535353958 / 1000000000000) (60535353959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (144324389336771 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10009478886 / 1000000000000) (10009478931 / 1000000000000), orderedInterval (-83467530322 / 1000000000000) (-83467530277 / 1000000000000)))) (orderedInterval (10595953363 / 1000000000000) (10595953401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (77618136586557 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-94578969736 / 1000000000000) (-94578941424 / 1000000000000), orderedInterval (65609682048 / 1000000000000) (65609710359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (210748339710671 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36649614156 / 1000000000000) (36649614157 / 1000000000000), orderedInterval (58937392830 / 1000000000000) (58937392831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (287758840445167 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-59493885971 / 1000000000000) (-59493885918 / 1000000000000), orderedInterval (-286715725 / 1000000000000) (-286715672 / 1000000000000)))) (orderedInterval (-4954414244 / 1000000000000) (-4954414175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (121675610663229 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90624269894 / 1000000000000) (90624269897 / 1000000000000), orderedInterval (11991412082 / 1000000000000) (11991412086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (494604602118109 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40541945109 / 1000000000000) (40541972531 / 1000000000000), orderedInterval (-20455630329 / 1000000000000) (-20455602907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (330372952227731 / 1600000000000) 2 (IntervalRat.scale (665 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4283864125 / 1000000000000) (-4283864115 / 1000000000000), orderedInterval (55371138368 / 1000000000000) (55371138378 / 1000000000000)))) (orderedInterval (10114766421 / 1000000000000) (10114774263 / 1000000000000))) = true
  rfl'

theorem compactCertificate292_chunkChecks2 :
    compactCertificate292.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate292.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate292_chunkChecks2_0
    compactCertificate292_chunkChecks2_1 compactCertificate292_chunkChecks2_2

theorem compactCertificate292_chunkChecks3_0 :
    compactCertificate292.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (665 / 4) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31295556858 / 1000000000000) (-31295556857 / 1000000000000), orderedInterval (-53290225306 / 1000000000000) (-53290225305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (195934396070833 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47610814250 / 1000000000000) (-47610814249 / 1000000000000), orderedInterval (-53952187771 / 1000000000000) (-53952187770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (63361157963089 / 320000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43267979161 / 1000000000000) (-43267979160 / 1000000000000), orderedInterval (-36538699240 / 1000000000000) (-36538699239 / 1000000000000)))) (orderedInterval (24846148086 / 1000000000000) (24846148104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (57173168106131 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123608280746 / 1000000000000) (-123608277552 / 1000000000000), orderedInterval (52084502869 / 1000000000000) (52084506063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (153575171604407 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47371985306 / 1000000000000) (47372002061 / 1000000000000), orderedInterval (-66492157426 / 1000000000000) (-66492140671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (416986465531419 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29882026741 / 1000000000000) (-29882026740 / 1000000000000), orderedInterval (-39310306714 / 1000000000000) (-39310306713 / 1000000000000)))) (orderedInterval (-10257209613 / 1000000000000) (-10257209445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (307150343208947 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51747384392 / 1000000000000) (-51747384391 / 1000000000000), orderedInterval (-25133091699 / 1000000000000) (-25133091698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (526307348298431 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6144001626 / 1000000000000) (6144001636 / 1000000000000), orderedInterval (-43570887888 / 1000000000000) (-43570887878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (387675610663229 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47384179502 / 1000000000000) (-47384179501 / 1000000000000), orderedInterval (-19451347679 / 1000000000000) (-19451347678 / 1000000000000)))) (orderedInterval (-8973409836 / 1000000000000) (-8973409780 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate292_chunkChecks3_1 :
    compactCertificate292.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (594794082014867 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (40068895117 / 1000000000000) (40068899673 / 1000000000000), orderedInterval (-10397660336 / 1000000000000) (-10397655780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (343404523363643 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (53225276857 / 1000000000000) (53225278074 / 1000000000000), orderedInterval (-11666057946 / 1000000000000) (-11666056729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (609377352882487 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40816529288 / 1000000000000) (-40816529177 / 1000000000000), orderedInterval (-2299721441 / 1000000000000) (-2299721330 / 1000000000000)))) (orderedInterval (-15223347238 / 1000000000000) (-15223337136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (569359369414003 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42210424089 / 1000000000000) (-42210423619 / 1000000000000), orderedInterval (2759666715 / 1000000000000) (2759667185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (406321711619299 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13208608731 / 1000000000000) (-13208608730 / 1000000000000), orderedInterval (-48268888166 / 1000000000000) (-48268888165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (460725514813221 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13360317619 / 1000000000000) (-13360317499 / 1000000000000), orderedInterval (45104762448 / 1000000000000) (45104762569 / 1000000000000)))) (orderedInterval (17947476671 / 1000000000000) (17947476849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (384104901201749 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44725028187 / 1000000000000) (44725060442 / 1000000000000), orderedInterval (-25618162128 / 1000000000000) (-25618129874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (339368328944729 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36871660936 / 1000000000000) (-36871631710 / 1000000000000), orderedInterval (40607470593 / 1000000000000) (40607499820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (98362169244171 / 320000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13043604387 / 1000000000000) (13043604388 / 1000000000000), orderedInterval (43578910443 / 1000000000000) (43578910444 / 1000000000000)))) (orderedInterval (-1301847159 / 1000000000000) (-1301842489 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate292_chunkChecks3_2 :
    compactCertificate292.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (272074936646737 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56700530041 / 1000000000000) (56700530043 / 1000000000000), orderedInterval (22829564480 / 1000000000000) (22829564481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (230640936942857 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27210388639 / 1000000000000) (27210388640 / 1000000000000), orderedInterval (60535353958 / 1000000000000) (60535353959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (144324389336771 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10009478886 / 1000000000000) (10009478931 / 1000000000000), orderedInterval (-83467530322 / 1000000000000) (-83467530277 / 1000000000000)))) (orderedInterval (6509636512 / 1000000000000) (6509636549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (77618136586557 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-94578969736 / 1000000000000) (-94578941424 / 1000000000000), orderedInterval (65609682048 / 1000000000000) (65609710359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (210748339710671 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36649614156 / 1000000000000) (36649614157 / 1000000000000), orderedInterval (58937392830 / 1000000000000) (58937392831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (287758840445167 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-59493885971 / 1000000000000) (-59493885918 / 1000000000000), orderedInterval (-286715725 / 1000000000000) (-286715672 / 1000000000000)))) (orderedInterval (697018231 / 1000000000000) (697018269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (121675610663229 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90624269894 / 1000000000000) (90624269897 / 1000000000000), orderedInterval (11991412082 / 1000000000000) (11991412086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (494604602118109 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40541945109 / 1000000000000) (40541972531 / 1000000000000), orderedInterval (-20455630329 / 1000000000000) (-20455602907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (330372952227731 / 1600000000000) 3 (IntervalRat.scale (665 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4283864125 / 1000000000000) (-4283864115 / 1000000000000), orderedInterval (55371138368 / 1000000000000) (55371138378 / 1000000000000)))) (orderedInterval (9131411438 / 1000000000000) (9131425986 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate292_chunkChecks3 :
    compactCertificate292.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate292.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate292_chunkChecks3_0
    compactCertificate292_chunkChecks3_1 compactCertificate292_chunkChecks3_2

theorem compactCertificate292_chunkChecks4_0 :
    compactCertificate292.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (665 / 4) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31295556858 / 1000000000000) (-31295556857 / 1000000000000), orderedInterval (-53290225306 / 1000000000000) (-53290225305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (195934396070833 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47610814250 / 1000000000000) (-47610814249 / 1000000000000), orderedInterval (-53952187771 / 1000000000000) (-53952187770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (63361157963089 / 320000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43267979161 / 1000000000000) (-43267979160 / 1000000000000), orderedInterval (-36538699240 / 1000000000000) (-36538699239 / 1000000000000)))) (orderedInterval (-17942074786 / 1000000000000) (-17942074764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (57173168106131 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123608280746 / 1000000000000) (-123608277552 / 1000000000000), orderedInterval (52084502869 / 1000000000000) (52084506063 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (153575171604407 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47371985306 / 1000000000000) (47372002061 / 1000000000000), orderedInterval (-66492157426 / 1000000000000) (-66492140671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (416986465531419 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29882026741 / 1000000000000) (-29882026740 / 1000000000000), orderedInterval (-39310306714 / 1000000000000) (-39310306713 / 1000000000000)))) (orderedInterval (13146778066 / 1000000000000) (13146778209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (307150343208947 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51747384392 / 1000000000000) (-51747384391 / 1000000000000), orderedInterval (-25133091699 / 1000000000000) (-25133091698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (526307348298431 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6144001626 / 1000000000000) (6144001636 / 1000000000000), orderedInterval (-43570887888 / 1000000000000) (-43570887878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (387675610663229 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47384179502 / 1000000000000) (-47384179501 / 1000000000000), orderedInterval (-19451347679 / 1000000000000) (-19451347678 / 1000000000000)))) (orderedInterval (-7963117177 / 1000000000000) (-7963117074 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate292_chunkChecks4_1 :
    compactCertificate292.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (594794082014867 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (40068895117 / 1000000000000) (40068899673 / 1000000000000), orderedInterval (-10397660336 / 1000000000000) (-10397655780 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (343404523363643 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (53225276857 / 1000000000000) (53225278074 / 1000000000000), orderedInterval (-11666057946 / 1000000000000) (-11666056729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (609377352882487 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-40816529288 / 1000000000000) (-40816529177 / 1000000000000), orderedInterval (-2299721441 / 1000000000000) (-2299721330 / 1000000000000)))) (orderedInterval (-326670154105 / 1000000000000) (-326670131643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (569359369414003 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42210424089 / 1000000000000) (-42210423619 / 1000000000000), orderedInterval (2759666715 / 1000000000000) (2759667185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (406321711619299 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13208608731 / 1000000000000) (-13208608730 / 1000000000000), orderedInterval (-48268888166 / 1000000000000) (-48268888165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (460725514813221 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13360317619 / 1000000000000) (-13360317499 / 1000000000000), orderedInterval (45104762448 / 1000000000000) (45104762569 / 1000000000000)))) (orderedInterval (9587443967 / 1000000000000) (9587444309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (384104901201749 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44725028187 / 1000000000000) (44725060442 / 1000000000000), orderedInterval (-25618162128 / 1000000000000) (-25618129874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (339368328944729 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36871660936 / 1000000000000) (-36871631710 / 1000000000000), orderedInterval (40607470593 / 1000000000000) (40607499820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (98362169244171 / 320000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13043604387 / 1000000000000) (13043604388 / 1000000000000), orderedInterval (43578910443 / 1000000000000) (43578910444 / 1000000000000)))) (orderedInterval (11754215626 / 1000000000000) (11754221816 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate292_chunkChecks4_2 :
    compactCertificate292.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (272074936646737 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56700530041 / 1000000000000) (56700530043 / 1000000000000), orderedInterval (22829564480 / 1000000000000) (22829564481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (230640936942857 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27210388639 / 1000000000000) (27210388640 / 1000000000000), orderedInterval (60535353958 / 1000000000000) (60535353959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (144324389336771 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10009478886 / 1000000000000) (10009478931 / 1000000000000), orderedInterval (-83467530322 / 1000000000000) (-83467530277 / 1000000000000)))) (orderedInterval (-10843180747 / 1000000000000) (-10843180711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (77618136586557 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-94578969736 / 1000000000000) (-94578941424 / 1000000000000), orderedInterval (65609682048 / 1000000000000) (65609710359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (210748339710671 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36649614156 / 1000000000000) (36649614157 / 1000000000000), orderedInterval (58937392830 / 1000000000000) (58937392831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (287758840445167 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-59493885971 / 1000000000000) (-59493885918 / 1000000000000), orderedInterval (-286715725 / 1000000000000) (-286715672 / 1000000000000)))) (orderedInterval (5921145606 / 1000000000000) (5921145636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (121675610663229 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90624269894 / 1000000000000) (90624269897 / 1000000000000), orderedInterval (11991412082 / 1000000000000) (11991412086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (494604602118109 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40541945109 / 1000000000000) (40541972531 / 1000000000000), orderedInterval (-20455630329 / 1000000000000) (-20455602907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (330372952227731 / 1600000000000) 4 (IntervalRat.scale (665 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4283864125 / 1000000000000) (-4283864115 / 1000000000000), orderedInterval (55371138368 / 1000000000000) (55371138378 / 1000000000000)))) (orderedInterval (-37622779879 / 1000000000000) (-37622752782 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate292_chunkChecks4 :
    compactCertificate292.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate292.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate292_chunkChecks4_0
    compactCertificate292_chunkChecks4_1 compactCertificate292_chunkChecks4_2

theorem compactCertificate292_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate292.chunkCheck r b = true :=
  compactCertificate292.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate292_chunkChecks0
    · exact compactCertificate292_chunkChecks1
    · exact compactCertificate292_chunkChecks2
    · exact compactCertificate292_chunkChecks3
    · exact compactCertificate292_chunkChecks4)

theorem compactCertificate292_coefficient0 :
    compactCertificate292.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate292_coefficient1 :
    compactCertificate292.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate292_coefficient2 :
    compactCertificate292.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate292_coefficient3 :
    compactCertificate292.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate292_coefficient4 :
    compactCertificate292.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate292_coefficients : ∀ r : Fin 5,
    compactCertificate292.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate292_coefficient0
  · exact compactCertificate292_coefficient1
  · exact compactCertificate292_coefficient2
  · exact compactCertificate292_coefficient3
  · exact compactCertificate292_coefficient4

theorem compactCertificate292_lower : (1 : ℚ) ≤ compactCertificate292.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate292, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate292_proves {t : ℝ} (ht : t ∈ compactCertificate292.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate292.proves compactCertificate292_states compactCertificate292_chunks
    compactCertificate292_coefficients compactCertificate292_lower ht

end Erdos232
