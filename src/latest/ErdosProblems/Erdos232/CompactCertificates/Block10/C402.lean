/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate402 : CompactCertificate where
  left := 273
  right := 274
  center := 547 / 2
  grid := fun i =>
    match i.val with
    | 0 => 87
    | 1 => 64
    | 2 => 104
    | 3 => 19
    | 4 => 50
    | 5 => 137
    | 6 => 101
    | 7 => 172
    | 8 => 127
    | 9 => 195
    | 10 => 112
    | 11 => 200
    | 12 => 186
    | 13 => 133
    | 14 => 151
    | 15 => 126
    | 16 => 111
    | 17 => 161
    | 18 => 89
    | 19 => 76
    | 20 => 47
    | 21 => 25
    | 22 => 69
    | 23 => 94
    | 24 => 40
    | 25 => 162
    | _ => 108
  point := fun i =>
    match i.val with
    | 0 => 547 / 2
    | 1 => 805835448501847 / 4000000000000
    | 2 => 260590627111351 / 800000000000
    | 3 => 235140774090629 / 4000000000000
    | 4 => 631621194493313 / 4000000000000
    | 5 => 1714974410869821 / 4000000000000
    | 6 => 1263242388987173 / 4000000000000
    | 7 => 2164587364806329 / 4000000000000
    | 8 => 1594425255885611 / 4000000000000
    | 9 => 2446258367384453 / 4000000000000
    | 10 => 1412347926916637 / 4000000000000
    | 11 => 2506236180652033 / 4000000000000
    | 12 => 2341650940371877 / 4000000000000
    | 13 => 1671112603426741 / 4000000000000
    | 14 => 1894863583479939 / 4000000000000
    | 15 => 1579739706446291 / 4000000000000
    | 16 => 1395747939344111 / 4000000000000
    | 17 => 404542154710989 / 800000000000
    | 18 => 1118984889817783 / 4000000000000
    | 19 => 948575883516863 / 4000000000000
    | 20 => 593574744114389 / 4000000000000
    | 21 => 319226471525163 / 4000000000000
    | 22 => 866761968584489 / 4000000000000
    | 23 => 1183489366342153 / 4000000000000
    | 24 => 500425255885611 / 4000000000000
    | 25 => 2034200882395531 / 4000000000000
    | _ => 1358751916305029 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-39698427492 / 1000000000000) (-39698427491 / 1000000000000), orderedInterval (-27344771939 / 1000000000000) (-27344771938 / 1000000000000))
    | 1 => (orderedInterval (52012548380 / 1000000000000) (52012548381 / 1000000000000), orderedInterval (21195459486 / 1000000000000) (21195459487 / 1000000000000))
    | 2 => (orderedInterval (-8884125888 / 1000000000000) (-8884125862 / 1000000000000), orderedInterval (43320273951 / 1000000000000) (43320273977 / 1000000000000))
    | 3 => (orderedInterval (12643075218 / 1000000000000) (12643075276 / 1000000000000), orderedInterval (-103403832999 / 1000000000000) (-103403832941 / 1000000000000))
    | 4 => (orderedInterval (63445691844 / 1000000000000) (63445691933 / 1000000000000), orderedInterval (-2706804108 / 1000000000000) (-2706804019 / 1000000000000))
    | 5 => (orderedInterval (29439608965 / 1000000000000) (29439644555 / 1000000000000), orderedInterval (-24897128964 / 1000000000000) (-24897093374 / 1000000000000))
    | 6 => (orderedInterval (29104214101 / 1000000000000) (29104227112 / 1000000000000), orderedInterval (-34233399780 / 1000000000000) (-34233386769 / 1000000000000))
    | 7 => (orderedInterval (34298166582 / 1000000000000) (34298167328 / 1000000000000), orderedInterval (-281235888 / 1000000000000) (-281235142 / 1000000000000))
    | 8 => (orderedInterval (-15898144475 / 1000000000000) (-15898144474 / 1000000000000), orderedInterval (-36645627291 / 1000000000000) (-36645627290 / 1000000000000))
    | 9 => (orderedInterval (8318833413 / 1000000000000) (8318833420 / 1000000000000), orderedInterval (-31179967570 / 1000000000000) (-31179967563 / 1000000000000))
    | 10 => (orderedInterval (38365678156 / 1000000000000) (38365705353 / 1000000000000), orderedInterval (-18250047329 / 1000000000000) (-18250020132 / 1000000000000))
    | 11 => (orderedInterval (-26370787628 / 1000000000000) (-26370750541 / 1000000000000), orderedInterval (17927434795 / 1000000000000) (17927471881 / 1000000000000))
    | 12 => (orderedInterval (31591431303 / 1000000000000) (31591451045 / 1000000000000), orderedInterval (-9484908091 / 1000000000000) (-9484888349 / 1000000000000))
    | 13 => (orderedInterval (-26073507041 / 1000000000000) (-26073507040 / 1000000000000), orderedInterval (-29020385579 / 1000000000000) (-29020385578 / 1000000000000))
    | 14 => (orderedInterval (-4408166933 / 1000000000000) (-4408166932 / 1000000000000), orderedInterval (-36388395654 / 1000000000000) (-36388395653 / 1000000000000))
    | 15 => (orderedInterval (-4832901162 / 1000000000000) (-4832901158 / 1000000000000), orderedInterval (39863432927 / 1000000000000) (39863432931 / 1000000000000))
    | 16 => (orderedInterval (-36062709505 / 1000000000000) (-36062709504 / 1000000000000), orderedInterval (-22837952137 / 1000000000000) (-22837952136 / 1000000000000))
    | 17 => (orderedInterval (-21934063062 / 1000000000000) (-21934063061 / 1000000000000), orderedInterval (-27868109186 / 1000000000000) (-27868109185 / 1000000000000))
    | 18 => (orderedInterval (-38224394286 / 1000000000000) (-38224394285 / 1000000000000), orderedInterval (-28472866029 / 1000000000000) (-28472866028 / 1000000000000))
    | 19 => (orderedInterval (-38310834155 / 1000000000000) (-38310773764 / 1000000000000), orderedInterval (34963551287 / 1000000000000) (34963611679 / 1000000000000))
    | 20 => (orderedInterval (-65424869926 / 1000000000000) (-65424869903 / 1000000000000), orderedInterval (-2883642428 / 1000000000000) (-2883642405 / 1000000000000))
    | 21 => (orderedInterval (-79227199619 / 1000000000000) (-79227189227 / 1000000000000), orderedInterval (41727299842 / 1000000000000) (41727310235 / 1000000000000))
    | 22 => (orderedInterval (-35142422675 / 1000000000000) (-35142422674 / 1000000000000), orderedInterval (-41185525226 / 1000000000000) (-41185525225 / 1000000000000))
    | 23 => (orderedInterval (45235539573 / 1000000000000) (45235539578 / 1000000000000), orderedInterval (10190669930 / 1000000000000) (10190669935 / 1000000000000))
    | 24 => (orderedInterval (16054665976 / 1000000000000) (16054665977 / 1000000000000), orderedInterval (69440617046 / 1000000000000) (69440617047 / 1000000000000))
    | 25 => (orderedInterval (13692122966 / 1000000000000) (13692122967 / 1000000000000), orderedInterval (32611051065 / 1000000000000) (32611051066 / 1000000000000))
    | _ => (orderedInterval (40043828786 / 1000000000000) (40043828788 / 1000000000000), orderedInterval (16391630489 / 1000000000000) (16391630490 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15771741533 / 1000000000000) (-15771741512 / 1000000000000)
      | 1 => orderedInterval (86490803 / 1000000000000) (86493371 / 1000000000000)
      | 2 => orderedInterval (-1442119500 / 1000000000000) (-1442119461 / 1000000000000)
      | 3 => orderedInterval (-2384338109 / 1000000000000) (-2384330712 / 1000000000000)
      | 4 => orderedInterval (-3013600888 / 1000000000000) (-3013600498 / 1000000000000)
      | 5 => orderedInterval (1446341613 / 1000000000000) (1446341640 / 1000000000000)
      | 6 => orderedInterval (6150255450 / 1000000000000) (6150258939 / 1000000000000)
      | 7 => orderedInterval (-1206590041 / 1000000000000) (-1206589816 / 1000000000000)
      | _ => orderedInterval (-8531064909 / 1000000000000) (-8531064833 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7665413412 / 1000000000000) (-7665413388 / 1000000000000)
      | 1 => orderedInterval (2958636389 / 1000000000000) (2958640396 / 1000000000000)
      | 2 => orderedInterval (-1273610796 / 1000000000000) (-1273610723 / 1000000000000)
      | 3 => orderedInterval (16481158255 / 1000000000000) (16481173161 / 1000000000000)
      | 4 => orderedInterval (-3506449507 / 1000000000000) (-3506448690 / 1000000000000)
      | 5 => orderedInterval (1012877430 / 1000000000000) (1012877468 / 1000000000000)
      | 6 => orderedInterval (2889752304 / 1000000000000) (2889755333 / 1000000000000)
      | 7 => orderedInterval (-329427904 / 1000000000000) (-329427818 / 1000000000000)
      | _ => orderedInterval (-8564304506 / 1000000000000) (-8564304399 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16239629412 / 1000000000000) (16239629440 / 1000000000000)
      | 1 => orderedInterval (4366377509 / 1000000000000) (4366383794 / 1000000000000)
      | 2 => orderedInterval (4962286045 / 1000000000000) (4962286183 / 1000000000000)
      | 3 => orderedInterval (22267065163 / 1000000000000) (22267096733 / 1000000000000)
      | 4 => orderedInterval (8311875911 / 1000000000000) (8311877635 / 1000000000000)
      | 5 => orderedInterval (-1326723611 / 1000000000000) (-1326723554 / 1000000000000)
      | 6 => orderedInterval (-7407914142 / 1000000000000) (-7407911500 / 1000000000000)
      | 7 => orderedInterval (3433346817 / 1000000000000) (3433346864 / 1000000000000)
      | _ => orderedInterval (15454372711 / 1000000000000) (15454372870 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (6405484132 / 1000000000000) (6405484164 / 1000000000000)
      | 1 => orderedInterval (-6826352144 / 1000000000000) (-6826342296 / 1000000000000)
      | 2 => orderedInterval (2656372676 / 1000000000000) (2656372942 / 1000000000000)
      | 3 => orderedInterval (-89754901805 / 1000000000000) (-89754832901 / 1000000000000)
      | 4 => orderedInterval (7114652161 / 1000000000000) (7114655812 / 1000000000000)
      | 5 => orderedInterval (414606532 / 1000000000000) (414606619 / 1000000000000)
      | 6 => orderedInterval (-3539554698 / 1000000000000) (-3539552401 / 1000000000000)
      | 7 => orderedInterval (530656680 / 1000000000000) (530656716 / 1000000000000)
      | _ => orderedInterval (22861476696 / 1000000000000) (22861476939 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16687975187 / 1000000000000) (-16687975149 / 1000000000000)
      | 1 => orderedInterval (-12331560864 / 1000000000000) (-12331545394 / 1000000000000)
      | 2 => orderedInterval (-17966255265 / 1000000000000) (-17966254750 / 1000000000000)
      | 3 => orderedInterval (-131655156123 / 1000000000000) (-131655002444 / 1000000000000)
      | 4 => orderedInterval (-25246162221 / 1000000000000) (-25246154456 / 1000000000000)
      | 5 => orderedInterval (-1340701204 / 1000000000000) (-1340701065 / 1000000000000)
      | 6 => orderedInterval (7756358050 / 1000000000000) (7756360057 / 1000000000000)
      | 7 => orderedInterval (-4427148155 / 1000000000000) (-4427148121 / 1000000000000)
      | _ => orderedInterval (-31364094790 / 1000000000000) (-31364094399 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-24666367114 / 1000000000000) (-24666352882 / 1000000000000)
    | 1 => orderedInterval (2003218253 / 1000000000000) (2003241340 / 1000000000000)
    | 2 => orderedInterval (66300315815 / 1000000000000) (66300358465 / 1000000000000)
    | 3 => orderedInterval (-60137559770 / 1000000000000) (-60137474406 / 1000000000000)
    | _ => orderedInterval (-233262695759 / 1000000000000) (-233262515721 / 1000000000000)

theorem compactCertificate402_stateChecks0 :
    compactCertificate402.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (547 / 2)) (orderedInterval (-39698427492 / 1000000000000) (-39698427491 / 1000000000000), orderedInterval (-27344771939 / 1000000000000) (-27344771938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (805835448501847 / 4000000000000)) (orderedInterval (52012548380 / 1000000000000) (52012548381 / 1000000000000), orderedInterval (21195459486 / 1000000000000) (21195459487 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (260590627111351 / 800000000000)) (orderedInterval (-8884125888 / 1000000000000) (-8884125862 / 1000000000000), orderedInterval (43320273951 / 1000000000000) (43320273977 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_stateChecks1 :
    compactCertificate402.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (235140774090629 / 4000000000000)) (orderedInterval (12643075218 / 1000000000000) (12643075276 / 1000000000000), orderedInterval (-103403832999 / 1000000000000) (-103403832941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (631621194493313 / 4000000000000)) (orderedInterval (63445691844 / 1000000000000) (63445691933 / 1000000000000), orderedInterval (-2706804108 / 1000000000000) (-2706804019 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1714974410869821 / 4000000000000)) (orderedInterval (29439608965 / 1000000000000) (29439644555 / 1000000000000), orderedInterval (-24897128964 / 1000000000000) (-24897093374 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_stateChecks2 :
    compactCertificate402.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1263242388987173 / 4000000000000)) (orderedInterval (29104214101 / 1000000000000) (29104227112 / 1000000000000), orderedInterval (-34233399780 / 1000000000000) (-34233386769 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2164587364806329 / 4000000000000)) (orderedInterval (34298166582 / 1000000000000) (34298167328 / 1000000000000), orderedInterval (-281235888 / 1000000000000) (-281235142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1594425255885611 / 4000000000000)) (orderedInterval (-15898144475 / 1000000000000) (-15898144474 / 1000000000000), orderedInterval (-36645627291 / 1000000000000) (-36645627290 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_stateChecks3 :
    compactCertificate402.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2446258367384453 / 4000000000000)) (orderedInterval (8318833413 / 1000000000000) (8318833420 / 1000000000000), orderedInterval (-31179967570 / 1000000000000) (-31179967563 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1412347926916637 / 4000000000000)) (orderedInterval (38365678156 / 1000000000000) (38365705353 / 1000000000000), orderedInterval (-18250047329 / 1000000000000) (-18250020132 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2506236180652033 / 4000000000000)) (orderedInterval (-26370787628 / 1000000000000) (-26370750541 / 1000000000000), orderedInterval (17927434795 / 1000000000000) (17927471881 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_stateChecks4 :
    compactCertificate402.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2341650940371877 / 4000000000000)) (orderedInterval (31591431303 / 1000000000000) (31591451045 / 1000000000000), orderedInterval (-9484908091 / 1000000000000) (-9484888349 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1671112603426741 / 4000000000000)) (orderedInterval (-26073507041 / 1000000000000) (-26073507040 / 1000000000000), orderedInterval (-29020385579 / 1000000000000) (-29020385578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1894863583479939 / 4000000000000)) (orderedInterval (-4408166933 / 1000000000000) (-4408166932 / 1000000000000), orderedInterval (-36388395654 / 1000000000000) (-36388395653 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_stateChecks5 :
    compactCertificate402.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1579739706446291 / 4000000000000)) (orderedInterval (-4832901162 / 1000000000000) (-4832901158 / 1000000000000), orderedInterval (39863432927 / 1000000000000) (39863432931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1395747939344111 / 4000000000000)) (orderedInterval (-36062709505 / 1000000000000) (-36062709504 / 1000000000000), orderedInterval (-22837952137 / 1000000000000) (-22837952136 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (404542154710989 / 800000000000)) (orderedInterval (-21934063062 / 1000000000000) (-21934063061 / 1000000000000), orderedInterval (-27868109186 / 1000000000000) (-27868109185 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_stateChecks6 :
    compactCertificate402.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1118984889817783 / 4000000000000)) (orderedInterval (-38224394286 / 1000000000000) (-38224394285 / 1000000000000), orderedInterval (-28472866029 / 1000000000000) (-28472866028 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (948575883516863 / 4000000000000)) (orderedInterval (-38310834155 / 1000000000000) (-38310773764 / 1000000000000), orderedInterval (34963551287 / 1000000000000) (34963611679 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (593574744114389 / 4000000000000)) (orderedInterval (-65424869926 / 1000000000000) (-65424869903 / 1000000000000), orderedInterval (-2883642428 / 1000000000000) (-2883642405 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_stateChecks7 :
    compactCertificate402.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (319226471525163 / 4000000000000)) (orderedInterval (-79227199619 / 1000000000000) (-79227189227 / 1000000000000), orderedInterval (41727299842 / 1000000000000) (41727310235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (866761968584489 / 4000000000000)) (orderedInterval (-35142422675 / 1000000000000) (-35142422674 / 1000000000000), orderedInterval (-41185525226 / 1000000000000) (-41185525225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1183489366342153 / 4000000000000)) (orderedInterval (45235539573 / 1000000000000) (45235539578 / 1000000000000), orderedInterval (10190669930 / 1000000000000) (10190669935 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_stateChecks8 :
    compactCertificate402.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (500425255885611 / 4000000000000)) (orderedInterval (16054665976 / 1000000000000) (16054665977 / 1000000000000), orderedInterval (69440617046 / 1000000000000) (69440617047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2034200882395531 / 4000000000000)) (orderedInterval (13692122966 / 1000000000000) (13692122967 / 1000000000000), orderedInterval (32611051065 / 1000000000000) (32611051066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1358751916305029 / 4000000000000)) (orderedInterval (40043828786 / 1000000000000) (40043828788 / 1000000000000), orderedInterval (16391630489 / 1000000000000) (16391630490 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_states : ∀ j,
    BesselStateValid (compactCertificate402.point j) (compactCertificate402.state j) :=
  compactCertificate402.statesValid_of_checks3 compactCertificate402_stateChecks0
    compactCertificate402_stateChecks1 compactCertificate402_stateChecks2
    compactCertificate402_stateChecks3 compactCertificate402_stateChecks4
    compactCertificate402_stateChecks5 compactCertificate402_stateChecks6
    compactCertificate402_stateChecks7 compactCertificate402_stateChecks8

theorem compactCertificate402_chunkChecks0_0 :
    compactCertificate402.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (547 / 2) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39698427492 / 1000000000000) (-39698427491 / 1000000000000), orderedInterval (-27344771939 / 1000000000000) (-27344771938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (805835448501847 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52012548380 / 1000000000000) (52012548381 / 1000000000000), orderedInterval (21195459486 / 1000000000000) (21195459487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (260590627111351 / 800000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8884125888 / 1000000000000) (-8884125862 / 1000000000000), orderedInterval (43320273951 / 1000000000000) (43320273977 / 1000000000000)))) (orderedInterval (-15771741533 / 1000000000000) (-15771741512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (235140774090629 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12643075218 / 1000000000000) (12643075276 / 1000000000000), orderedInterval (-103403832999 / 1000000000000) (-103403832941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (631621194493313 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63445691844 / 1000000000000) (63445691933 / 1000000000000), orderedInterval (-2706804108 / 1000000000000) (-2706804019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1714974410869821 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29439608965 / 1000000000000) (29439644555 / 1000000000000), orderedInterval (-24897128964 / 1000000000000) (-24897093374 / 1000000000000)))) (orderedInterval (86490803 / 1000000000000) (86493371 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1263242388987173 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29104214101 / 1000000000000) (29104227112 / 1000000000000), orderedInterval (-34233399780 / 1000000000000) (-34233386769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2164587364806329 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34298166582 / 1000000000000) (34298167328 / 1000000000000), orderedInterval (-281235888 / 1000000000000) (-281235142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1594425255885611 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15898144475 / 1000000000000) (-15898144474 / 1000000000000), orderedInterval (-36645627291 / 1000000000000) (-36645627290 / 1000000000000)))) (orderedInterval (-1442119500 / 1000000000000) (-1442119461 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks0_1 :
    compactCertificate402.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2446258367384453 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8318833413 / 1000000000000) (8318833420 / 1000000000000), orderedInterval (-31179967570 / 1000000000000) (-31179967563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1412347926916637 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38365678156 / 1000000000000) (38365705353 / 1000000000000), orderedInterval (-18250047329 / 1000000000000) (-18250020132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2506236180652033 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26370787628 / 1000000000000) (-26370750541 / 1000000000000), orderedInterval (17927434795 / 1000000000000) (17927471881 / 1000000000000)))) (orderedInterval (-2384338109 / 1000000000000) (-2384330712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2341650940371877 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31591431303 / 1000000000000) (31591451045 / 1000000000000), orderedInterval (-9484908091 / 1000000000000) (-9484888349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1671112603426741 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26073507041 / 1000000000000) (-26073507040 / 1000000000000), orderedInterval (-29020385579 / 1000000000000) (-29020385578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1894863583479939 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4408166933 / 1000000000000) (-4408166932 / 1000000000000), orderedInterval (-36388395654 / 1000000000000) (-36388395653 / 1000000000000)))) (orderedInterval (-3013600888 / 1000000000000) (-3013600498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1579739706446291 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4832901162 / 1000000000000) (-4832901158 / 1000000000000), orderedInterval (39863432927 / 1000000000000) (39863432931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1395747939344111 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36062709505 / 1000000000000) (-36062709504 / 1000000000000), orderedInterval (-22837952137 / 1000000000000) (-22837952136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (404542154710989 / 800000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21934063062 / 1000000000000) (-21934063061 / 1000000000000), orderedInterval (-27868109186 / 1000000000000) (-27868109185 / 1000000000000)))) (orderedInterval (1446341613 / 1000000000000) (1446341640 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks0_2 :
    compactCertificate402.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1118984889817783 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38224394286 / 1000000000000) (-38224394285 / 1000000000000), orderedInterval (-28472866029 / 1000000000000) (-28472866028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (948575883516863 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38310834155 / 1000000000000) (-38310773764 / 1000000000000), orderedInterval (34963551287 / 1000000000000) (34963611679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (593574744114389 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65424869926 / 1000000000000) (-65424869903 / 1000000000000), orderedInterval (-2883642428 / 1000000000000) (-2883642405 / 1000000000000)))) (orderedInterval (6150255450 / 1000000000000) (6150258939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (319226471525163 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-79227199619 / 1000000000000) (-79227189227 / 1000000000000), orderedInterval (41727299842 / 1000000000000) (41727310235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (866761968584489 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35142422675 / 1000000000000) (-35142422674 / 1000000000000), orderedInterval (-41185525226 / 1000000000000) (-41185525225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1183489366342153 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45235539573 / 1000000000000) (45235539578 / 1000000000000), orderedInterval (10190669930 / 1000000000000) (10190669935 / 1000000000000)))) (orderedInterval (-1206590041 / 1000000000000) (-1206589816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (500425255885611 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16054665976 / 1000000000000) (16054665977 / 1000000000000), orderedInterval (69440617046 / 1000000000000) (69440617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2034200882395531 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13692122966 / 1000000000000) (13692122967 / 1000000000000), orderedInterval (32611051065 / 1000000000000) (32611051066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1358751916305029 / 4000000000000) 0 (IntervalRat.scale (547 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40043828786 / 1000000000000) (40043828788 / 1000000000000), orderedInterval (16391630489 / 1000000000000) (16391630490 / 1000000000000)))) (orderedInterval (-8531064909 / 1000000000000) (-8531064833 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks0 :
    compactCertificate402.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate402.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate402_chunkChecks0_0
    compactCertificate402_chunkChecks0_1 compactCertificate402_chunkChecks0_2

theorem compactCertificate402_chunkChecks1_0 :
    compactCertificate402.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (547 / 2) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39698427492 / 1000000000000) (-39698427491 / 1000000000000), orderedInterval (-27344771939 / 1000000000000) (-27344771938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (805835448501847 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52012548380 / 1000000000000) (52012548381 / 1000000000000), orderedInterval (21195459486 / 1000000000000) (21195459487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (260590627111351 / 800000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8884125888 / 1000000000000) (-8884125862 / 1000000000000), orderedInterval (43320273951 / 1000000000000) (43320273977 / 1000000000000)))) (orderedInterval (-7665413412 / 1000000000000) (-7665413388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (235140774090629 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12643075218 / 1000000000000) (12643075276 / 1000000000000), orderedInterval (-103403832999 / 1000000000000) (-103403832941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (631621194493313 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63445691844 / 1000000000000) (63445691933 / 1000000000000), orderedInterval (-2706804108 / 1000000000000) (-2706804019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1714974410869821 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29439608965 / 1000000000000) (29439644555 / 1000000000000), orderedInterval (-24897128964 / 1000000000000) (-24897093374 / 1000000000000)))) (orderedInterval (2958636389 / 1000000000000) (2958640396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1263242388987173 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29104214101 / 1000000000000) (29104227112 / 1000000000000), orderedInterval (-34233399780 / 1000000000000) (-34233386769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2164587364806329 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34298166582 / 1000000000000) (34298167328 / 1000000000000), orderedInterval (-281235888 / 1000000000000) (-281235142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1594425255885611 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15898144475 / 1000000000000) (-15898144474 / 1000000000000), orderedInterval (-36645627291 / 1000000000000) (-36645627290 / 1000000000000)))) (orderedInterval (-1273610796 / 1000000000000) (-1273610723 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks1_1 :
    compactCertificate402.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2446258367384453 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8318833413 / 1000000000000) (8318833420 / 1000000000000), orderedInterval (-31179967570 / 1000000000000) (-31179967563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1412347926916637 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38365678156 / 1000000000000) (38365705353 / 1000000000000), orderedInterval (-18250047329 / 1000000000000) (-18250020132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2506236180652033 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26370787628 / 1000000000000) (-26370750541 / 1000000000000), orderedInterval (17927434795 / 1000000000000) (17927471881 / 1000000000000)))) (orderedInterval (16481158255 / 1000000000000) (16481173161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2341650940371877 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31591431303 / 1000000000000) (31591451045 / 1000000000000), orderedInterval (-9484908091 / 1000000000000) (-9484888349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1671112603426741 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26073507041 / 1000000000000) (-26073507040 / 1000000000000), orderedInterval (-29020385579 / 1000000000000) (-29020385578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1894863583479939 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4408166933 / 1000000000000) (-4408166932 / 1000000000000), orderedInterval (-36388395654 / 1000000000000) (-36388395653 / 1000000000000)))) (orderedInterval (-3506449507 / 1000000000000) (-3506448690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1579739706446291 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4832901162 / 1000000000000) (-4832901158 / 1000000000000), orderedInterval (39863432927 / 1000000000000) (39863432931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1395747939344111 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36062709505 / 1000000000000) (-36062709504 / 1000000000000), orderedInterval (-22837952137 / 1000000000000) (-22837952136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (404542154710989 / 800000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21934063062 / 1000000000000) (-21934063061 / 1000000000000), orderedInterval (-27868109186 / 1000000000000) (-27868109185 / 1000000000000)))) (orderedInterval (1012877430 / 1000000000000) (1012877468 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks1_2 :
    compactCertificate402.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1118984889817783 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38224394286 / 1000000000000) (-38224394285 / 1000000000000), orderedInterval (-28472866029 / 1000000000000) (-28472866028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (948575883516863 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38310834155 / 1000000000000) (-38310773764 / 1000000000000), orderedInterval (34963551287 / 1000000000000) (34963611679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (593574744114389 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65424869926 / 1000000000000) (-65424869903 / 1000000000000), orderedInterval (-2883642428 / 1000000000000) (-2883642405 / 1000000000000)))) (orderedInterval (2889752304 / 1000000000000) (2889755333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (319226471525163 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-79227199619 / 1000000000000) (-79227189227 / 1000000000000), orderedInterval (41727299842 / 1000000000000) (41727310235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (866761968584489 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35142422675 / 1000000000000) (-35142422674 / 1000000000000), orderedInterval (-41185525226 / 1000000000000) (-41185525225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1183489366342153 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45235539573 / 1000000000000) (45235539578 / 1000000000000), orderedInterval (10190669930 / 1000000000000) (10190669935 / 1000000000000)))) (orderedInterval (-329427904 / 1000000000000) (-329427818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (500425255885611 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16054665976 / 1000000000000) (16054665977 / 1000000000000), orderedInterval (69440617046 / 1000000000000) (69440617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2034200882395531 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13692122966 / 1000000000000) (13692122967 / 1000000000000), orderedInterval (32611051065 / 1000000000000) (32611051066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1358751916305029 / 4000000000000) 1 (IntervalRat.scale (547 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40043828786 / 1000000000000) (40043828788 / 1000000000000), orderedInterval (16391630489 / 1000000000000) (16391630490 / 1000000000000)))) (orderedInterval (-8564304506 / 1000000000000) (-8564304399 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks1 :
    compactCertificate402.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate402.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate402_chunkChecks1_0
    compactCertificate402_chunkChecks1_1 compactCertificate402_chunkChecks1_2

theorem compactCertificate402_chunkChecks2_0 :
    compactCertificate402.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (547 / 2) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39698427492 / 1000000000000) (-39698427491 / 1000000000000), orderedInterval (-27344771939 / 1000000000000) (-27344771938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (805835448501847 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52012548380 / 1000000000000) (52012548381 / 1000000000000), orderedInterval (21195459486 / 1000000000000) (21195459487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (260590627111351 / 800000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8884125888 / 1000000000000) (-8884125862 / 1000000000000), orderedInterval (43320273951 / 1000000000000) (43320273977 / 1000000000000)))) (orderedInterval (16239629412 / 1000000000000) (16239629440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (235140774090629 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12643075218 / 1000000000000) (12643075276 / 1000000000000), orderedInterval (-103403832999 / 1000000000000) (-103403832941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (631621194493313 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63445691844 / 1000000000000) (63445691933 / 1000000000000), orderedInterval (-2706804108 / 1000000000000) (-2706804019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1714974410869821 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29439608965 / 1000000000000) (29439644555 / 1000000000000), orderedInterval (-24897128964 / 1000000000000) (-24897093374 / 1000000000000)))) (orderedInterval (4366377509 / 1000000000000) (4366383794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1263242388987173 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29104214101 / 1000000000000) (29104227112 / 1000000000000), orderedInterval (-34233399780 / 1000000000000) (-34233386769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2164587364806329 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34298166582 / 1000000000000) (34298167328 / 1000000000000), orderedInterval (-281235888 / 1000000000000) (-281235142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1594425255885611 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15898144475 / 1000000000000) (-15898144474 / 1000000000000), orderedInterval (-36645627291 / 1000000000000) (-36645627290 / 1000000000000)))) (orderedInterval (4962286045 / 1000000000000) (4962286183 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks2_1 :
    compactCertificate402.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2446258367384453 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8318833413 / 1000000000000) (8318833420 / 1000000000000), orderedInterval (-31179967570 / 1000000000000) (-31179967563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1412347926916637 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38365678156 / 1000000000000) (38365705353 / 1000000000000), orderedInterval (-18250047329 / 1000000000000) (-18250020132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2506236180652033 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26370787628 / 1000000000000) (-26370750541 / 1000000000000), orderedInterval (17927434795 / 1000000000000) (17927471881 / 1000000000000)))) (orderedInterval (22267065163 / 1000000000000) (22267096733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2341650940371877 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31591431303 / 1000000000000) (31591451045 / 1000000000000), orderedInterval (-9484908091 / 1000000000000) (-9484888349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1671112603426741 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26073507041 / 1000000000000) (-26073507040 / 1000000000000), orderedInterval (-29020385579 / 1000000000000) (-29020385578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1894863583479939 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4408166933 / 1000000000000) (-4408166932 / 1000000000000), orderedInterval (-36388395654 / 1000000000000) (-36388395653 / 1000000000000)))) (orderedInterval (8311875911 / 1000000000000) (8311877635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1579739706446291 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4832901162 / 1000000000000) (-4832901158 / 1000000000000), orderedInterval (39863432927 / 1000000000000) (39863432931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1395747939344111 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36062709505 / 1000000000000) (-36062709504 / 1000000000000), orderedInterval (-22837952137 / 1000000000000) (-22837952136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (404542154710989 / 800000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21934063062 / 1000000000000) (-21934063061 / 1000000000000), orderedInterval (-27868109186 / 1000000000000) (-27868109185 / 1000000000000)))) (orderedInterval (-1326723611 / 1000000000000) (-1326723554 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks2_2 :
    compactCertificate402.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1118984889817783 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38224394286 / 1000000000000) (-38224394285 / 1000000000000), orderedInterval (-28472866029 / 1000000000000) (-28472866028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (948575883516863 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38310834155 / 1000000000000) (-38310773764 / 1000000000000), orderedInterval (34963551287 / 1000000000000) (34963611679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (593574744114389 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65424869926 / 1000000000000) (-65424869903 / 1000000000000), orderedInterval (-2883642428 / 1000000000000) (-2883642405 / 1000000000000)))) (orderedInterval (-7407914142 / 1000000000000) (-7407911500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (319226471525163 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-79227199619 / 1000000000000) (-79227189227 / 1000000000000), orderedInterval (41727299842 / 1000000000000) (41727310235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (866761968584489 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35142422675 / 1000000000000) (-35142422674 / 1000000000000), orderedInterval (-41185525226 / 1000000000000) (-41185525225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1183489366342153 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45235539573 / 1000000000000) (45235539578 / 1000000000000), orderedInterval (10190669930 / 1000000000000) (10190669935 / 1000000000000)))) (orderedInterval (3433346817 / 1000000000000) (3433346864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (500425255885611 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16054665976 / 1000000000000) (16054665977 / 1000000000000), orderedInterval (69440617046 / 1000000000000) (69440617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2034200882395531 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13692122966 / 1000000000000) (13692122967 / 1000000000000), orderedInterval (32611051065 / 1000000000000) (32611051066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1358751916305029 / 4000000000000) 2 (IntervalRat.scale (547 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40043828786 / 1000000000000) (40043828788 / 1000000000000), orderedInterval (16391630489 / 1000000000000) (16391630490 / 1000000000000)))) (orderedInterval (15454372711 / 1000000000000) (15454372870 / 1000000000000))) = true
  rfl'

theorem compactCertificate402_chunkChecks2 :
    compactCertificate402.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate402.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate402_chunkChecks2_0
    compactCertificate402_chunkChecks2_1 compactCertificate402_chunkChecks2_2

theorem compactCertificate402_chunkChecks3_0 :
    compactCertificate402.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (547 / 2) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39698427492 / 1000000000000) (-39698427491 / 1000000000000), orderedInterval (-27344771939 / 1000000000000) (-27344771938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (805835448501847 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52012548380 / 1000000000000) (52012548381 / 1000000000000), orderedInterval (21195459486 / 1000000000000) (21195459487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (260590627111351 / 800000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8884125888 / 1000000000000) (-8884125862 / 1000000000000), orderedInterval (43320273951 / 1000000000000) (43320273977 / 1000000000000)))) (orderedInterval (6405484132 / 1000000000000) (6405484164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (235140774090629 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12643075218 / 1000000000000) (12643075276 / 1000000000000), orderedInterval (-103403832999 / 1000000000000) (-103403832941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (631621194493313 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63445691844 / 1000000000000) (63445691933 / 1000000000000), orderedInterval (-2706804108 / 1000000000000) (-2706804019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1714974410869821 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29439608965 / 1000000000000) (29439644555 / 1000000000000), orderedInterval (-24897128964 / 1000000000000) (-24897093374 / 1000000000000)))) (orderedInterval (-6826352144 / 1000000000000) (-6826342296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1263242388987173 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29104214101 / 1000000000000) (29104227112 / 1000000000000), orderedInterval (-34233399780 / 1000000000000) (-34233386769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2164587364806329 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34298166582 / 1000000000000) (34298167328 / 1000000000000), orderedInterval (-281235888 / 1000000000000) (-281235142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1594425255885611 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15898144475 / 1000000000000) (-15898144474 / 1000000000000), orderedInterval (-36645627291 / 1000000000000) (-36645627290 / 1000000000000)))) (orderedInterval (2656372676 / 1000000000000) (2656372942 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate402_chunkChecks3_1 :
    compactCertificate402.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2446258367384453 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8318833413 / 1000000000000) (8318833420 / 1000000000000), orderedInterval (-31179967570 / 1000000000000) (-31179967563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1412347926916637 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38365678156 / 1000000000000) (38365705353 / 1000000000000), orderedInterval (-18250047329 / 1000000000000) (-18250020132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2506236180652033 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26370787628 / 1000000000000) (-26370750541 / 1000000000000), orderedInterval (17927434795 / 1000000000000) (17927471881 / 1000000000000)))) (orderedInterval (-89754901805 / 1000000000000) (-89754832901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2341650940371877 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31591431303 / 1000000000000) (31591451045 / 1000000000000), orderedInterval (-9484908091 / 1000000000000) (-9484888349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1671112603426741 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26073507041 / 1000000000000) (-26073507040 / 1000000000000), orderedInterval (-29020385579 / 1000000000000) (-29020385578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1894863583479939 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4408166933 / 1000000000000) (-4408166932 / 1000000000000), orderedInterval (-36388395654 / 1000000000000) (-36388395653 / 1000000000000)))) (orderedInterval (7114652161 / 1000000000000) (7114655812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1579739706446291 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4832901162 / 1000000000000) (-4832901158 / 1000000000000), orderedInterval (39863432927 / 1000000000000) (39863432931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1395747939344111 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36062709505 / 1000000000000) (-36062709504 / 1000000000000), orderedInterval (-22837952137 / 1000000000000) (-22837952136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (404542154710989 / 800000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21934063062 / 1000000000000) (-21934063061 / 1000000000000), orderedInterval (-27868109186 / 1000000000000) (-27868109185 / 1000000000000)))) (orderedInterval (414606532 / 1000000000000) (414606619 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate402_chunkChecks3_2 :
    compactCertificate402.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1118984889817783 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38224394286 / 1000000000000) (-38224394285 / 1000000000000), orderedInterval (-28472866029 / 1000000000000) (-28472866028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (948575883516863 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38310834155 / 1000000000000) (-38310773764 / 1000000000000), orderedInterval (34963551287 / 1000000000000) (34963611679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (593574744114389 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65424869926 / 1000000000000) (-65424869903 / 1000000000000), orderedInterval (-2883642428 / 1000000000000) (-2883642405 / 1000000000000)))) (orderedInterval (-3539554698 / 1000000000000) (-3539552401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (319226471525163 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-79227199619 / 1000000000000) (-79227189227 / 1000000000000), orderedInterval (41727299842 / 1000000000000) (41727310235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (866761968584489 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35142422675 / 1000000000000) (-35142422674 / 1000000000000), orderedInterval (-41185525226 / 1000000000000) (-41185525225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1183489366342153 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45235539573 / 1000000000000) (45235539578 / 1000000000000), orderedInterval (10190669930 / 1000000000000) (10190669935 / 1000000000000)))) (orderedInterval (530656680 / 1000000000000) (530656716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (500425255885611 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16054665976 / 1000000000000) (16054665977 / 1000000000000), orderedInterval (69440617046 / 1000000000000) (69440617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2034200882395531 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13692122966 / 1000000000000) (13692122967 / 1000000000000), orderedInterval (32611051065 / 1000000000000) (32611051066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1358751916305029 / 4000000000000) 3 (IntervalRat.scale (547 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40043828786 / 1000000000000) (40043828788 / 1000000000000), orderedInterval (16391630489 / 1000000000000) (16391630490 / 1000000000000)))) (orderedInterval (22861476696 / 1000000000000) (22861476939 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate402_chunkChecks3 :
    compactCertificate402.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate402.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate402_chunkChecks3_0
    compactCertificate402_chunkChecks3_1 compactCertificate402_chunkChecks3_2

theorem compactCertificate402_chunkChecks4_0 :
    compactCertificate402.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (547 / 2) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39698427492 / 1000000000000) (-39698427491 / 1000000000000), orderedInterval (-27344771939 / 1000000000000) (-27344771938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (805835448501847 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52012548380 / 1000000000000) (52012548381 / 1000000000000), orderedInterval (21195459486 / 1000000000000) (21195459487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (260590627111351 / 800000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8884125888 / 1000000000000) (-8884125862 / 1000000000000), orderedInterval (43320273951 / 1000000000000) (43320273977 / 1000000000000)))) (orderedInterval (-16687975187 / 1000000000000) (-16687975149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (235140774090629 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12643075218 / 1000000000000) (12643075276 / 1000000000000), orderedInterval (-103403832999 / 1000000000000) (-103403832941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (631621194493313 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (63445691844 / 1000000000000) (63445691933 / 1000000000000), orderedInterval (-2706804108 / 1000000000000) (-2706804019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1714974410869821 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29439608965 / 1000000000000) (29439644555 / 1000000000000), orderedInterval (-24897128964 / 1000000000000) (-24897093374 / 1000000000000)))) (orderedInterval (-12331560864 / 1000000000000) (-12331545394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1263242388987173 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29104214101 / 1000000000000) (29104227112 / 1000000000000), orderedInterval (-34233399780 / 1000000000000) (-34233386769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2164587364806329 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (34298166582 / 1000000000000) (34298167328 / 1000000000000), orderedInterval (-281235888 / 1000000000000) (-281235142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1594425255885611 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-15898144475 / 1000000000000) (-15898144474 / 1000000000000), orderedInterval (-36645627291 / 1000000000000) (-36645627290 / 1000000000000)))) (orderedInterval (-17966255265 / 1000000000000) (-17966254750 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate402_chunkChecks4_1 :
    compactCertificate402.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2446258367384453 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8318833413 / 1000000000000) (8318833420 / 1000000000000), orderedInterval (-31179967570 / 1000000000000) (-31179967563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1412347926916637 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38365678156 / 1000000000000) (38365705353 / 1000000000000), orderedInterval (-18250047329 / 1000000000000) (-18250020132 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2506236180652033 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26370787628 / 1000000000000) (-26370750541 / 1000000000000), orderedInterval (17927434795 / 1000000000000) (17927471881 / 1000000000000)))) (orderedInterval (-131655156123 / 1000000000000) (-131655002444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2341650940371877 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31591431303 / 1000000000000) (31591451045 / 1000000000000), orderedInterval (-9484908091 / 1000000000000) (-9484888349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1671112603426741 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26073507041 / 1000000000000) (-26073507040 / 1000000000000), orderedInterval (-29020385579 / 1000000000000) (-29020385578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1894863583479939 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4408166933 / 1000000000000) (-4408166932 / 1000000000000), orderedInterval (-36388395654 / 1000000000000) (-36388395653 / 1000000000000)))) (orderedInterval (-25246162221 / 1000000000000) (-25246154456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1579739706446291 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4832901162 / 1000000000000) (-4832901158 / 1000000000000), orderedInterval (39863432927 / 1000000000000) (39863432931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1395747939344111 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36062709505 / 1000000000000) (-36062709504 / 1000000000000), orderedInterval (-22837952137 / 1000000000000) (-22837952136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (404542154710989 / 800000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21934063062 / 1000000000000) (-21934063061 / 1000000000000), orderedInterval (-27868109186 / 1000000000000) (-27868109185 / 1000000000000)))) (orderedInterval (-1340701204 / 1000000000000) (-1340701065 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate402_chunkChecks4_2 :
    compactCertificate402.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1118984889817783 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38224394286 / 1000000000000) (-38224394285 / 1000000000000), orderedInterval (-28472866029 / 1000000000000) (-28472866028 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (948575883516863 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38310834155 / 1000000000000) (-38310773764 / 1000000000000), orderedInterval (34963551287 / 1000000000000) (34963611679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (593574744114389 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65424869926 / 1000000000000) (-65424869903 / 1000000000000), orderedInterval (-2883642428 / 1000000000000) (-2883642405 / 1000000000000)))) (orderedInterval (7756358050 / 1000000000000) (7756360057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (319226471525163 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-79227199619 / 1000000000000) (-79227189227 / 1000000000000), orderedInterval (41727299842 / 1000000000000) (41727310235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (866761968584489 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35142422675 / 1000000000000) (-35142422674 / 1000000000000), orderedInterval (-41185525226 / 1000000000000) (-41185525225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1183489366342153 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45235539573 / 1000000000000) (45235539578 / 1000000000000), orderedInterval (10190669930 / 1000000000000) (10190669935 / 1000000000000)))) (orderedInterval (-4427148155 / 1000000000000) (-4427148121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (500425255885611 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16054665976 / 1000000000000) (16054665977 / 1000000000000), orderedInterval (69440617046 / 1000000000000) (69440617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2034200882395531 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13692122966 / 1000000000000) (13692122967 / 1000000000000), orderedInterval (32611051065 / 1000000000000) (32611051066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1358751916305029 / 4000000000000) 4 (IntervalRat.scale (547 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40043828786 / 1000000000000) (40043828788 / 1000000000000), orderedInterval (16391630489 / 1000000000000) (16391630490 / 1000000000000)))) (orderedInterval (-31364094790 / 1000000000000) (-31364094399 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate402_chunkChecks4 :
    compactCertificate402.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate402.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate402_chunkChecks4_0
    compactCertificate402_chunkChecks4_1 compactCertificate402_chunkChecks4_2

theorem compactCertificate402_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate402.chunkCheck r b = true :=
  compactCertificate402.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate402_chunkChecks0
    · exact compactCertificate402_chunkChecks1
    · exact compactCertificate402_chunkChecks2
    · exact compactCertificate402_chunkChecks3
    · exact compactCertificate402_chunkChecks4)

theorem compactCertificate402_coefficient0 :
    compactCertificate402.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate402_coefficient1 :
    compactCertificate402.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate402_coefficient2 :
    compactCertificate402.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate402_coefficient3 :
    compactCertificate402.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate402_coefficient4 :
    compactCertificate402.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate402_coefficients : ∀ r : Fin 5,
    compactCertificate402.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate402_coefficient0
  · exact compactCertificate402_coefficient1
  · exact compactCertificate402_coefficient2
  · exact compactCertificate402_coefficient3
  · exact compactCertificate402_coefficient4

theorem compactCertificate402_lower : (1 : ℚ) ≤ compactCertificate402.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate402, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate402_proves {t : ℝ} (ht : t ∈ compactCertificate402.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate402.proves compactCertificate402_states compactCertificate402_chunks
    compactCertificate402_coefficients compactCertificate402_lower ht

end Erdos232
