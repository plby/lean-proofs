/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate311 : CompactCertificate where
  left := 184
  right := 185
  center := 369 / 2
  grid := fun i =>
    match i.val with
    | 0 => 59
    | 1 => 43
    | 2 => 70
    | 3 => 13
    | 4 => 34
    | 5 => 92
    | 6 => 68
    | 7 => 116
    | 8 => 86
    | 9 => 131
    | 10 => 76
    | 11 => 135
    | 12 => 126
    | 13 => 90
    | 14 => 102
    | 15 => 85
    | 16 => 75
    | 17 => 109
    | 18 => 60
    | 19 => 51
    | 20 => 32
    | 21 => 17
    | 22 => 47
    | 23 => 64
    | 24 => 27
    | 25 => 109
    | _ => 73
  point := fun i =>
    match i.val with
    | 0 => 369 / 2
    | 1 => 543607459775469 / 4000000000000
    | 2 => 175791483371277 / 800000000000
    | 3 => 158623300986183 / 4000000000000
    | 4 => 426084498661851 / 4000000000000
    | 5 => 1156902299105967 / 4000000000000
    | 6 => 852168997324071 / 4000000000000
    | 7 => 1460206101670083 / 4000000000000
    | 8 => 1075581205524297 / 4000000000000
    | 9 => 1650218167394631 / 4000000000000
    | 10 => 952753903166799 / 4000000000000
    | 11 => 1690678520403291 / 4000000000000
    | 12 => 1579651182810279 / 4000000000000
    | 13 => 1127313620958807 / 4000000000000
    | 14 => 1278253495985553 / 4000000000000
    | 15 => 1065674500326657 / 4000000000000
    | 16 => 941555739703797 / 4000000000000
    | 17 => 272899552263903 / 800000000000
    | 18 => 754854523478541 / 4000000000000
    | 19 => 639898539337701 / 4000000000000
    | 20 => 400418794475703 / 4000000000000
    | 21 => 215346559401801 / 4000000000000
    | 22 => 584707799648403 / 4000000000000
    | 23 => 798368512212531 / 4000000000000
    | 24 => 337581205524297 / 4000000000000
    | 25 => 1372248858508137 / 4000000000000
    | _ => 916598641894983 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (4064320814 / 1000000000000) (4064320824 / 1000000000000), orderedInterval (-58611419773 / 1000000000000) (-58611419763 / 1000000000000))
    | 1 => (orderedInterval (-68417440866 / 1000000000000) (-68417440803 / 1000000000000), orderedInterval (2103753377 / 1000000000000) (2103753440 / 1000000000000))
    | 2 => (orderedInterval (30953607678 / 1000000000000) (30953607679 / 1000000000000), orderedInterval (43964047120 / 1000000000000) (43964047121 / 1000000000000))
    | 3 => (orderedInterval (49645467601 / 1000000000000) (49645469920 / 1000000000000), orderedInterval (-117201309692 / 1000000000000) (-117201307374 / 1000000000000))
    | 4 => (orderedInterval (36464528442 / 1000000000000) (36464528443 / 1000000000000), orderedInterval (67996574810 / 1000000000000) (67996574811 / 1000000000000))
    | 5 => (orderedInterval (39068304709 / 1000000000000) (39068304710 / 1000000000000), orderedInterval (25909081453 / 1000000000000) (25909081454 / 1000000000000))
    | 6 => (orderedInterval (10793765751 / 1000000000000) (10793765752 / 1000000000000), orderedInterval (53563236469 / 1000000000000) (53563236470 / 1000000000000))
    | 7 => (orderedInterval (41233705467 / 1000000000000) (41233705489 / 1000000000000), orderedInterval (6553936356 / 1000000000000) (6553936378 / 1000000000000))
    | 8 => (orderedInterval (-23187951802 / 1000000000000) (-23187949940 / 1000000000000), orderedInterval (42819966005 / 1000000000000) (42819967866 / 1000000000000))
    | 9 => (orderedInterval (-38333960342 / 1000000000000) (-38333956322 / 1000000000000), orderedInterval (8626855380 / 1000000000000) (8626859400 / 1000000000000))
    | 10 => (orderedInterval (10893740269 / 1000000000000) (10893740270 / 1000000000000), orderedInterval (50515119751 / 1000000000000) (50515119752 / 1000000000000))
    | 11 => (orderedInterval (23803281564 / 1000000000000) (23803286321 / 1000000000000), orderedInterval (-30680918507 / 1000000000000) (-30680913751 / 1000000000000))
    | 12 => (orderedInterval (-5713884378 / 1000000000000) (-5713884372 / 1000000000000), orderedInterval (39748954045 / 1000000000000) (39748954051 / 1000000000000))
    | 13 => (orderedInterval (-6160228260 / 1000000000000) (-6160228248 / 1000000000000), orderedInterval (47137847678 / 1000000000000) (47137847690 / 1000000000000))
    | 14 => (orderedInterval (-4192472063 / 1000000000000) (-4192472058 / 1000000000000), orderedInterval (44442812554 / 1000000000000) (44442812559 / 1000000000000))
    | 15 => (orderedInterval (-8182361856 / 1000000000000) (-8182361855 / 1000000000000), orderedInterval (-48178001521 / 1000000000000) (-48178001520 / 1000000000000))
    | 16 => (orderedInterval (-27375176858 / 1000000000000) (-27375176857 / 1000000000000), orderedInterval (-44158890979 / 1000000000000) (-44158890978 / 1000000000000))
    | 17 => (orderedInterval (21619748236 / 1000000000000) (21619749914 / 1000000000000), orderedInterval (-37432579535 / 1000000000000) (-37432577857 / 1000000000000))
    | 18 => (orderedInterval (48961788391 / 1000000000000) (48961788392 / 1000000000000), orderedInterval (31114607940 / 1000000000000) (31114607941 / 1000000000000))
    | 19 => (orderedInterval (-32326469132 / 1000000000000) (-32326469131 / 1000000000000), orderedInterval (-54070110940 / 1000000000000) (-54070110939 / 1000000000000))
    | 20 => (orderedInterval (27934493903 / 1000000000000) (27934493904 / 1000000000000), orderedInterval (74554943253 / 1000000000000) (74554943254 / 1000000000000))
    | 21 => (orderedInterval (-101840491138 / 1000000000000) (-101840491137 / 1000000000000), orderedInterval (-37174561173 / 1000000000000) (-37174561171 / 1000000000000))
    | 22 => (orderedInterval (42177992190 / 1000000000000) (42178018415 / 1000000000000), orderedInterval (-50900084071 / 1000000000000) (-50900057846 / 1000000000000))
    | 23 => (orderedInterval (-35732465141 / 1000000000000) (-35732446289 / 1000000000000), orderedInterval (43825040255 / 1000000000000) (43825059107 / 1000000000000))
    | 24 => (orderedInterval (-30287805748 / 1000000000000) (-30287805747 / 1000000000000), orderedInterval (-81221163389 / 1000000000000) (-81221163388 / 1000000000000))
    | 25 => (orderedInterval (-42546973222 / 1000000000000) (-42546973203 / 1000000000000), orderedInterval (-6679719641 / 1000000000000) (-6679719621 / 1000000000000))
    | _ => (orderedInterval (-29685209516 / 1000000000000) (-29685209515 / 1000000000000), orderedInterval (-43489494019 / 1000000000000) (-43489494018 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (2789829651 / 1000000000000) (2789829669 / 1000000000000)
      | 1 => orderedInterval (-1984586317 / 1000000000000) (-1984586269 / 1000000000000)
      | 2 => orderedInterval (-1832219504 / 1000000000000) (-1832219447 / 1000000000000)
      | 3 => orderedInterval (11002394390 / 1000000000000) (11002395854 / 1000000000000)
      | 4 => orderedInterval (-458159281 / 1000000000000) (-458159257 / 1000000000000)
      | 5 => orderedInterval (2025654133 / 1000000000000) (2025654194 / 1000000000000)
      | 6 => orderedInterval (-5089528184 / 1000000000000) (-5089528137 / 1000000000000)
      | 7 => orderedInterval (3662103996 / 1000000000000) (3662106058 / 1000000000000)
      | _ => orderedInterval (8850547136 / 1000000000000) (8850547189 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-20144463885 / 1000000000000) (-20144463866 / 1000000000000)
      | 1 => orderedInterval (-1180669548 / 1000000000000) (-1180669516 / 1000000000000)
      | 2 => orderedInterval (1108280502 / 1000000000000) (1108280588 / 1000000000000)
      | 3 => orderedInterval (-8587433716 / 1000000000000) (-8587430418 / 1000000000000)
      | 4 => orderedInterval (4883411992 / 1000000000000) (4883412030 / 1000000000000)
      | 5 => orderedInterval (648683277 / 1000000000000) (648683383 / 1000000000000)
      | 6 => orderedInterval (-1118145674 / 1000000000000) (-1118145630 / 1000000000000)
      | 7 => orderedInterval (-2518242731 / 1000000000000) (-2518240676 / 1000000000000)
      | _ => orderedInterval (10921550975 / 1000000000000) (10921551051 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3732386051 / 1000000000000) (-3732386029 / 1000000000000)
      | 1 => orderedInterval (6412627205 / 1000000000000) (6412627242 / 1000000000000)
      | 2 => orderedInterval (6163310405 / 1000000000000) (6163310536 / 1000000000000)
      | 3 => orderedInterval (-53114791298 / 1000000000000) (-53114783835 / 1000000000000)
      | 4 => orderedInterval (796517847 / 1000000000000) (796517910 / 1000000000000)
      | 5 => orderedInterval (-4248767280 / 1000000000000) (-4248767094 / 1000000000000)
      | 6 => orderedInterval (6553053074 / 1000000000000) (6553053115 / 1000000000000)
      | 7 => orderedInterval (-2750650460 / 1000000000000) (-2750648364 / 1000000000000)
      | _ => orderedInterval (-20587160633 / 1000000000000) (-20587160520 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18884882956 / 1000000000000) (18884882981 / 1000000000000)
      | 1 => orderedInterval (6570231284 / 1000000000000) (6570231337 / 1000000000000)
      | 2 => orderedInterval (-1671208917 / 1000000000000) (-1671208713 / 1000000000000)
      | 3 => orderedInterval (61810843222 / 1000000000000) (61810860088 / 1000000000000)
      | 4 => orderedInterval (-7685959713 / 1000000000000) (-7685959607 / 1000000000000)
      | 5 => orderedInterval (2507949743 / 1000000000000) (2507950075 / 1000000000000)
      | 6 => orderedInterval (2905487253 / 1000000000000) (2905487294 / 1000000000000)
      | 7 => orderedInterval (3675666516 / 1000000000000) (3675668673 / 1000000000000)
      | _ => orderedInterval (-18970005167 / 1000000000000) (-18970004992 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (4873191422 / 1000000000000) (4873191449 / 1000000000000)
      | 1 => orderedInterval (-16696534322 / 1000000000000) (-16696534240 / 1000000000000)
      | 2 => orderedInterval (-22002037119 / 1000000000000) (-22002036796 / 1000000000000)
      | 3 => orderedInterval (265058440805 / 1000000000000) (265058479044 / 1000000000000)
      | 4 => orderedInterval (-732038778 / 1000000000000) (-732038595 / 1000000000000)
      | 5 => orderedInterval (10181301392 / 1000000000000) (10181301991 / 1000000000000)
      | 6 => orderedInterval (-7486975254 / 1000000000000) (-7486975214 / 1000000000000)
      | 7 => orderedInterval (3347258811 / 1000000000000) (3347261069 / 1000000000000)
      | _ => orderedInterval (54851178248 / 1000000000000) (54851178530 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (18966036020 / 1000000000000) (18966039854 / 1000000000000)
    | 1 => orderedInterval (-15987028808 / 1000000000000) (-15987023054 / 1000000000000)
    | 2 => orderedInterval (-64508247191 / 1000000000000) (-64508237039 / 1000000000000)
    | 3 => orderedInterval (68027887177 / 1000000000000) (68027907136 / 1000000000000)
    | _ => orderedInterval (291393785205 / 1000000000000) (291393827238 / 1000000000000)

theorem compactCertificate311_stateChecks0 :
    compactCertificate311.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (369 / 2)) (orderedInterval (4064320814 / 1000000000000) (4064320824 / 1000000000000), orderedInterval (-58611419773 / 1000000000000) (-58611419763 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543607459775469 / 4000000000000)) (orderedInterval (-68417440866 / 1000000000000) (-68417440803 / 1000000000000), orderedInterval (2103753377 / 1000000000000) (2103753440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (175791483371277 / 800000000000)) (orderedInterval (30953607678 / 1000000000000) (30953607679 / 1000000000000), orderedInterval (43964047120 / 1000000000000) (43964047121 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_stateChecks1 :
    compactCertificate311.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (158623300986183 / 4000000000000)) (orderedInterval (49645467601 / 1000000000000) (49645469920 / 1000000000000), orderedInterval (-117201309692 / 1000000000000) (-117201307374 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (426084498661851 / 4000000000000)) (orderedInterval (36464528442 / 1000000000000) (36464528443 / 1000000000000), orderedInterval (67996574810 / 1000000000000) (67996574811 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1156902299105967 / 4000000000000)) (orderedInterval (39068304709 / 1000000000000) (39068304710 / 1000000000000), orderedInterval (25909081453 / 1000000000000) (25909081454 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_stateChecks2 :
    compactCertificate311.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (852168997324071 / 4000000000000)) (orderedInterval (10793765751 / 1000000000000) (10793765752 / 1000000000000), orderedInterval (53563236469 / 1000000000000) (53563236470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1460206101670083 / 4000000000000)) (orderedInterval (41233705467 / 1000000000000) (41233705489 / 1000000000000), orderedInterval (6553936356 / 1000000000000) (6553936378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1075581205524297 / 4000000000000)) (orderedInterval (-23187951802 / 1000000000000) (-23187949940 / 1000000000000), orderedInterval (42819966005 / 1000000000000) (42819967866 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_stateChecks3 :
    compactCertificate311.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1650218167394631 / 4000000000000)) (orderedInterval (-38333960342 / 1000000000000) (-38333956322 / 1000000000000), orderedInterval (8626855380 / 1000000000000) (8626859400 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (952753903166799 / 4000000000000)) (orderedInterval (10893740269 / 1000000000000) (10893740270 / 1000000000000), orderedInterval (50515119751 / 1000000000000) (50515119752 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1690678520403291 / 4000000000000)) (orderedInterval (23803281564 / 1000000000000) (23803286321 / 1000000000000), orderedInterval (-30680918507 / 1000000000000) (-30680913751 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_stateChecks4 :
    compactCertificate311.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1579651182810279 / 4000000000000)) (orderedInterval (-5713884378 / 1000000000000) (-5713884372 / 1000000000000), orderedInterval (39748954045 / 1000000000000) (39748954051 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1127313620958807 / 4000000000000)) (orderedInterval (-6160228260 / 1000000000000) (-6160228248 / 1000000000000), orderedInterval (47137847678 / 1000000000000) (47137847690 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1278253495985553 / 4000000000000)) (orderedInterval (-4192472063 / 1000000000000) (-4192472058 / 1000000000000), orderedInterval (44442812554 / 1000000000000) (44442812559 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_stateChecks5 :
    compactCertificate311.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1065674500326657 / 4000000000000)) (orderedInterval (-8182361856 / 1000000000000) (-8182361855 / 1000000000000), orderedInterval (-48178001521 / 1000000000000) (-48178001520 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (941555739703797 / 4000000000000)) (orderedInterval (-27375176858 / 1000000000000) (-27375176857 / 1000000000000), orderedInterval (-44158890979 / 1000000000000) (-44158890978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (272899552263903 / 800000000000)) (orderedInterval (21619748236 / 1000000000000) (21619749914 / 1000000000000), orderedInterval (-37432579535 / 1000000000000) (-37432577857 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_stateChecks6 :
    compactCertificate311.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (754854523478541 / 4000000000000)) (orderedInterval (48961788391 / 1000000000000) (48961788392 / 1000000000000), orderedInterval (31114607940 / 1000000000000) (31114607941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (639898539337701 / 4000000000000)) (orderedInterval (-32326469132 / 1000000000000) (-32326469131 / 1000000000000), orderedInterval (-54070110940 / 1000000000000) (-54070110939 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (400418794475703 / 4000000000000)) (orderedInterval (27934493903 / 1000000000000) (27934493904 / 1000000000000), orderedInterval (74554943253 / 1000000000000) (74554943254 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_stateChecks7 :
    compactCertificate311.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (215346559401801 / 4000000000000)) (orderedInterval (-101840491138 / 1000000000000) (-101840491137 / 1000000000000), orderedInterval (-37174561173 / 1000000000000) (-37174561171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (584707799648403 / 4000000000000)) (orderedInterval (42177992190 / 1000000000000) (42178018415 / 1000000000000), orderedInterval (-50900084071 / 1000000000000) (-50900057846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (798368512212531 / 4000000000000)) (orderedInterval (-35732465141 / 1000000000000) (-35732446289 / 1000000000000), orderedInterval (43825040255 / 1000000000000) (43825059107 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_stateChecks8 :
    compactCertificate311.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (337581205524297 / 4000000000000)) (orderedInterval (-30287805748 / 1000000000000) (-30287805747 / 1000000000000), orderedInterval (-81221163389 / 1000000000000) (-81221163388 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1372248858508137 / 4000000000000)) (orderedInterval (-42546973222 / 1000000000000) (-42546973203 / 1000000000000), orderedInterval (-6679719641 / 1000000000000) (-6679719621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (916598641894983 / 4000000000000)) (orderedInterval (-29685209516 / 1000000000000) (-29685209515 / 1000000000000), orderedInterval (-43489494019 / 1000000000000) (-43489494018 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_states : ∀ j,
    BesselStateValid (compactCertificate311.point j) (compactCertificate311.state j) :=
  compactCertificate311.statesValid_of_checks3 compactCertificate311_stateChecks0
    compactCertificate311_stateChecks1 compactCertificate311_stateChecks2
    compactCertificate311_stateChecks3 compactCertificate311_stateChecks4
    compactCertificate311_stateChecks5 compactCertificate311_stateChecks6
    compactCertificate311_stateChecks7 compactCertificate311_stateChecks8

theorem compactCertificate311_chunkChecks0_0 :
    compactCertificate311.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (369 / 2) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4064320814 / 1000000000000) (4064320824 / 1000000000000), orderedInterval (-58611419773 / 1000000000000) (-58611419763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (543607459775469 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68417440866 / 1000000000000) (-68417440803 / 1000000000000), orderedInterval (2103753377 / 1000000000000) (2103753440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (175791483371277 / 800000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30953607678 / 1000000000000) (30953607679 / 1000000000000), orderedInterval (43964047120 / 1000000000000) (43964047121 / 1000000000000)))) (orderedInterval (2789829651 / 1000000000000) (2789829669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (158623300986183 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49645467601 / 1000000000000) (49645469920 / 1000000000000), orderedInterval (-117201309692 / 1000000000000) (-117201307374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (426084498661851 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36464528442 / 1000000000000) (36464528443 / 1000000000000), orderedInterval (67996574810 / 1000000000000) (67996574811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1156902299105967 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39068304709 / 1000000000000) (39068304710 / 1000000000000), orderedInterval (25909081453 / 1000000000000) (25909081454 / 1000000000000)))) (orderedInterval (-1984586317 / 1000000000000) (-1984586269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (852168997324071 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10793765751 / 1000000000000) (10793765752 / 1000000000000), orderedInterval (53563236469 / 1000000000000) (53563236470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1460206101670083 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41233705467 / 1000000000000) (41233705489 / 1000000000000), orderedInterval (6553936356 / 1000000000000) (6553936378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1075581205524297 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23187951802 / 1000000000000) (-23187949940 / 1000000000000), orderedInterval (42819966005 / 1000000000000) (42819967866 / 1000000000000)))) (orderedInterval (-1832219504 / 1000000000000) (-1832219447 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks0_1 :
    compactCertificate311.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1650218167394631 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38333960342 / 1000000000000) (-38333956322 / 1000000000000), orderedInterval (8626855380 / 1000000000000) (8626859400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (952753903166799 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10893740269 / 1000000000000) (10893740270 / 1000000000000), orderedInterval (50515119751 / 1000000000000) (50515119752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1690678520403291 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23803281564 / 1000000000000) (23803286321 / 1000000000000), orderedInterval (-30680918507 / 1000000000000) (-30680913751 / 1000000000000)))) (orderedInterval (11002394390 / 1000000000000) (11002395854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1579651182810279 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5713884378 / 1000000000000) (-5713884372 / 1000000000000), orderedInterval (39748954045 / 1000000000000) (39748954051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1127313620958807 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6160228260 / 1000000000000) (-6160228248 / 1000000000000), orderedInterval (47137847678 / 1000000000000) (47137847690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1278253495985553 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4192472063 / 1000000000000) (-4192472058 / 1000000000000), orderedInterval (44442812554 / 1000000000000) (44442812559 / 1000000000000)))) (orderedInterval (-458159281 / 1000000000000) (-458159257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1065674500326657 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8182361856 / 1000000000000) (-8182361855 / 1000000000000), orderedInterval (-48178001521 / 1000000000000) (-48178001520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (941555739703797 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27375176858 / 1000000000000) (-27375176857 / 1000000000000), orderedInterval (-44158890979 / 1000000000000) (-44158890978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (272899552263903 / 800000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21619748236 / 1000000000000) (21619749914 / 1000000000000), orderedInterval (-37432579535 / 1000000000000) (-37432577857 / 1000000000000)))) (orderedInterval (2025654133 / 1000000000000) (2025654194 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks0_2 :
    compactCertificate311.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (754854523478541 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48961788391 / 1000000000000) (48961788392 / 1000000000000), orderedInterval (31114607940 / 1000000000000) (31114607941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (639898539337701 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32326469132 / 1000000000000) (-32326469131 / 1000000000000), orderedInterval (-54070110940 / 1000000000000) (-54070110939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (400418794475703 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27934493903 / 1000000000000) (27934493904 / 1000000000000), orderedInterval (74554943253 / 1000000000000) (74554943254 / 1000000000000)))) (orderedInterval (-5089528184 / 1000000000000) (-5089528137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (215346559401801 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101840491138 / 1000000000000) (-101840491137 / 1000000000000), orderedInterval (-37174561173 / 1000000000000) (-37174561171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (584707799648403 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42177992190 / 1000000000000) (42178018415 / 1000000000000), orderedInterval (-50900084071 / 1000000000000) (-50900057846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (798368512212531 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35732465141 / 1000000000000) (-35732446289 / 1000000000000), orderedInterval (43825040255 / 1000000000000) (43825059107 / 1000000000000)))) (orderedInterval (3662103996 / 1000000000000) (3662106058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (337581205524297 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30287805748 / 1000000000000) (-30287805747 / 1000000000000), orderedInterval (-81221163389 / 1000000000000) (-81221163388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1372248858508137 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42546973222 / 1000000000000) (-42546973203 / 1000000000000), orderedInterval (-6679719641 / 1000000000000) (-6679719621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (916598641894983 / 4000000000000) 0 (IntervalRat.scale (369 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29685209516 / 1000000000000) (-29685209515 / 1000000000000), orderedInterval (-43489494019 / 1000000000000) (-43489494018 / 1000000000000)))) (orderedInterval (8850547136 / 1000000000000) (8850547189 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks0 :
    compactCertificate311.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate311.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate311_chunkChecks0_0
    compactCertificate311_chunkChecks0_1 compactCertificate311_chunkChecks0_2

theorem compactCertificate311_chunkChecks1_0 :
    compactCertificate311.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (369 / 2) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4064320814 / 1000000000000) (4064320824 / 1000000000000), orderedInterval (-58611419773 / 1000000000000) (-58611419763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (543607459775469 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68417440866 / 1000000000000) (-68417440803 / 1000000000000), orderedInterval (2103753377 / 1000000000000) (2103753440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (175791483371277 / 800000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30953607678 / 1000000000000) (30953607679 / 1000000000000), orderedInterval (43964047120 / 1000000000000) (43964047121 / 1000000000000)))) (orderedInterval (-20144463885 / 1000000000000) (-20144463866 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (158623300986183 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49645467601 / 1000000000000) (49645469920 / 1000000000000), orderedInterval (-117201309692 / 1000000000000) (-117201307374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (426084498661851 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36464528442 / 1000000000000) (36464528443 / 1000000000000), orderedInterval (67996574810 / 1000000000000) (67996574811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1156902299105967 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39068304709 / 1000000000000) (39068304710 / 1000000000000), orderedInterval (25909081453 / 1000000000000) (25909081454 / 1000000000000)))) (orderedInterval (-1180669548 / 1000000000000) (-1180669516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (852168997324071 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10793765751 / 1000000000000) (10793765752 / 1000000000000), orderedInterval (53563236469 / 1000000000000) (53563236470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1460206101670083 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41233705467 / 1000000000000) (41233705489 / 1000000000000), orderedInterval (6553936356 / 1000000000000) (6553936378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1075581205524297 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23187951802 / 1000000000000) (-23187949940 / 1000000000000), orderedInterval (42819966005 / 1000000000000) (42819967866 / 1000000000000)))) (orderedInterval (1108280502 / 1000000000000) (1108280588 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks1_1 :
    compactCertificate311.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1650218167394631 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38333960342 / 1000000000000) (-38333956322 / 1000000000000), orderedInterval (8626855380 / 1000000000000) (8626859400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (952753903166799 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10893740269 / 1000000000000) (10893740270 / 1000000000000), orderedInterval (50515119751 / 1000000000000) (50515119752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1690678520403291 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23803281564 / 1000000000000) (23803286321 / 1000000000000), orderedInterval (-30680918507 / 1000000000000) (-30680913751 / 1000000000000)))) (orderedInterval (-8587433716 / 1000000000000) (-8587430418 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1579651182810279 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5713884378 / 1000000000000) (-5713884372 / 1000000000000), orderedInterval (39748954045 / 1000000000000) (39748954051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1127313620958807 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6160228260 / 1000000000000) (-6160228248 / 1000000000000), orderedInterval (47137847678 / 1000000000000) (47137847690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1278253495985553 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4192472063 / 1000000000000) (-4192472058 / 1000000000000), orderedInterval (44442812554 / 1000000000000) (44442812559 / 1000000000000)))) (orderedInterval (4883411992 / 1000000000000) (4883412030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1065674500326657 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8182361856 / 1000000000000) (-8182361855 / 1000000000000), orderedInterval (-48178001521 / 1000000000000) (-48178001520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (941555739703797 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27375176858 / 1000000000000) (-27375176857 / 1000000000000), orderedInterval (-44158890979 / 1000000000000) (-44158890978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (272899552263903 / 800000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21619748236 / 1000000000000) (21619749914 / 1000000000000), orderedInterval (-37432579535 / 1000000000000) (-37432577857 / 1000000000000)))) (orderedInterval (648683277 / 1000000000000) (648683383 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks1_2 :
    compactCertificate311.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (754854523478541 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48961788391 / 1000000000000) (48961788392 / 1000000000000), orderedInterval (31114607940 / 1000000000000) (31114607941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (639898539337701 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32326469132 / 1000000000000) (-32326469131 / 1000000000000), orderedInterval (-54070110940 / 1000000000000) (-54070110939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (400418794475703 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27934493903 / 1000000000000) (27934493904 / 1000000000000), orderedInterval (74554943253 / 1000000000000) (74554943254 / 1000000000000)))) (orderedInterval (-1118145674 / 1000000000000) (-1118145630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (215346559401801 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101840491138 / 1000000000000) (-101840491137 / 1000000000000), orderedInterval (-37174561173 / 1000000000000) (-37174561171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (584707799648403 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42177992190 / 1000000000000) (42178018415 / 1000000000000), orderedInterval (-50900084071 / 1000000000000) (-50900057846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (798368512212531 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35732465141 / 1000000000000) (-35732446289 / 1000000000000), orderedInterval (43825040255 / 1000000000000) (43825059107 / 1000000000000)))) (orderedInterval (-2518242731 / 1000000000000) (-2518240676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (337581205524297 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30287805748 / 1000000000000) (-30287805747 / 1000000000000), orderedInterval (-81221163389 / 1000000000000) (-81221163388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1372248858508137 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42546973222 / 1000000000000) (-42546973203 / 1000000000000), orderedInterval (-6679719641 / 1000000000000) (-6679719621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (916598641894983 / 4000000000000) 1 (IntervalRat.scale (369 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29685209516 / 1000000000000) (-29685209515 / 1000000000000), orderedInterval (-43489494019 / 1000000000000) (-43489494018 / 1000000000000)))) (orderedInterval (10921550975 / 1000000000000) (10921551051 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks1 :
    compactCertificate311.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate311.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate311_chunkChecks1_0
    compactCertificate311_chunkChecks1_1 compactCertificate311_chunkChecks1_2

theorem compactCertificate311_chunkChecks2_0 :
    compactCertificate311.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (369 / 2) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4064320814 / 1000000000000) (4064320824 / 1000000000000), orderedInterval (-58611419773 / 1000000000000) (-58611419763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (543607459775469 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68417440866 / 1000000000000) (-68417440803 / 1000000000000), orderedInterval (2103753377 / 1000000000000) (2103753440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (175791483371277 / 800000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30953607678 / 1000000000000) (30953607679 / 1000000000000), orderedInterval (43964047120 / 1000000000000) (43964047121 / 1000000000000)))) (orderedInterval (-3732386051 / 1000000000000) (-3732386029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (158623300986183 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49645467601 / 1000000000000) (49645469920 / 1000000000000), orderedInterval (-117201309692 / 1000000000000) (-117201307374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (426084498661851 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36464528442 / 1000000000000) (36464528443 / 1000000000000), orderedInterval (67996574810 / 1000000000000) (67996574811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1156902299105967 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39068304709 / 1000000000000) (39068304710 / 1000000000000), orderedInterval (25909081453 / 1000000000000) (25909081454 / 1000000000000)))) (orderedInterval (6412627205 / 1000000000000) (6412627242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (852168997324071 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10793765751 / 1000000000000) (10793765752 / 1000000000000), orderedInterval (53563236469 / 1000000000000) (53563236470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1460206101670083 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41233705467 / 1000000000000) (41233705489 / 1000000000000), orderedInterval (6553936356 / 1000000000000) (6553936378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1075581205524297 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23187951802 / 1000000000000) (-23187949940 / 1000000000000), orderedInterval (42819966005 / 1000000000000) (42819967866 / 1000000000000)))) (orderedInterval (6163310405 / 1000000000000) (6163310536 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks2_1 :
    compactCertificate311.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1650218167394631 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38333960342 / 1000000000000) (-38333956322 / 1000000000000), orderedInterval (8626855380 / 1000000000000) (8626859400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (952753903166799 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10893740269 / 1000000000000) (10893740270 / 1000000000000), orderedInterval (50515119751 / 1000000000000) (50515119752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1690678520403291 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23803281564 / 1000000000000) (23803286321 / 1000000000000), orderedInterval (-30680918507 / 1000000000000) (-30680913751 / 1000000000000)))) (orderedInterval (-53114791298 / 1000000000000) (-53114783835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1579651182810279 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5713884378 / 1000000000000) (-5713884372 / 1000000000000), orderedInterval (39748954045 / 1000000000000) (39748954051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1127313620958807 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6160228260 / 1000000000000) (-6160228248 / 1000000000000), orderedInterval (47137847678 / 1000000000000) (47137847690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1278253495985553 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4192472063 / 1000000000000) (-4192472058 / 1000000000000), orderedInterval (44442812554 / 1000000000000) (44442812559 / 1000000000000)))) (orderedInterval (796517847 / 1000000000000) (796517910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1065674500326657 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8182361856 / 1000000000000) (-8182361855 / 1000000000000), orderedInterval (-48178001521 / 1000000000000) (-48178001520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (941555739703797 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27375176858 / 1000000000000) (-27375176857 / 1000000000000), orderedInterval (-44158890979 / 1000000000000) (-44158890978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (272899552263903 / 800000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21619748236 / 1000000000000) (21619749914 / 1000000000000), orderedInterval (-37432579535 / 1000000000000) (-37432577857 / 1000000000000)))) (orderedInterval (-4248767280 / 1000000000000) (-4248767094 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks2_2 :
    compactCertificate311.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (754854523478541 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48961788391 / 1000000000000) (48961788392 / 1000000000000), orderedInterval (31114607940 / 1000000000000) (31114607941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (639898539337701 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32326469132 / 1000000000000) (-32326469131 / 1000000000000), orderedInterval (-54070110940 / 1000000000000) (-54070110939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (400418794475703 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27934493903 / 1000000000000) (27934493904 / 1000000000000), orderedInterval (74554943253 / 1000000000000) (74554943254 / 1000000000000)))) (orderedInterval (6553053074 / 1000000000000) (6553053115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (215346559401801 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101840491138 / 1000000000000) (-101840491137 / 1000000000000), orderedInterval (-37174561173 / 1000000000000) (-37174561171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (584707799648403 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42177992190 / 1000000000000) (42178018415 / 1000000000000), orderedInterval (-50900084071 / 1000000000000) (-50900057846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (798368512212531 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35732465141 / 1000000000000) (-35732446289 / 1000000000000), orderedInterval (43825040255 / 1000000000000) (43825059107 / 1000000000000)))) (orderedInterval (-2750650460 / 1000000000000) (-2750648364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (337581205524297 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30287805748 / 1000000000000) (-30287805747 / 1000000000000), orderedInterval (-81221163389 / 1000000000000) (-81221163388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1372248858508137 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42546973222 / 1000000000000) (-42546973203 / 1000000000000), orderedInterval (-6679719641 / 1000000000000) (-6679719621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (916598641894983 / 4000000000000) 2 (IntervalRat.scale (369 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29685209516 / 1000000000000) (-29685209515 / 1000000000000), orderedInterval (-43489494019 / 1000000000000) (-43489494018 / 1000000000000)))) (orderedInterval (-20587160633 / 1000000000000) (-20587160520 / 1000000000000))) = true
  rfl'

theorem compactCertificate311_chunkChecks2 :
    compactCertificate311.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate311.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate311_chunkChecks2_0
    compactCertificate311_chunkChecks2_1 compactCertificate311_chunkChecks2_2

theorem compactCertificate311_chunkChecks3_0 :
    compactCertificate311.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (369 / 2) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4064320814 / 1000000000000) (4064320824 / 1000000000000), orderedInterval (-58611419773 / 1000000000000) (-58611419763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (543607459775469 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68417440866 / 1000000000000) (-68417440803 / 1000000000000), orderedInterval (2103753377 / 1000000000000) (2103753440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (175791483371277 / 800000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30953607678 / 1000000000000) (30953607679 / 1000000000000), orderedInterval (43964047120 / 1000000000000) (43964047121 / 1000000000000)))) (orderedInterval (18884882956 / 1000000000000) (18884882981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (158623300986183 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49645467601 / 1000000000000) (49645469920 / 1000000000000), orderedInterval (-117201309692 / 1000000000000) (-117201307374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (426084498661851 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36464528442 / 1000000000000) (36464528443 / 1000000000000), orderedInterval (67996574810 / 1000000000000) (67996574811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1156902299105967 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39068304709 / 1000000000000) (39068304710 / 1000000000000), orderedInterval (25909081453 / 1000000000000) (25909081454 / 1000000000000)))) (orderedInterval (6570231284 / 1000000000000) (6570231337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (852168997324071 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10793765751 / 1000000000000) (10793765752 / 1000000000000), orderedInterval (53563236469 / 1000000000000) (53563236470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1460206101670083 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41233705467 / 1000000000000) (41233705489 / 1000000000000), orderedInterval (6553936356 / 1000000000000) (6553936378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1075581205524297 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23187951802 / 1000000000000) (-23187949940 / 1000000000000), orderedInterval (42819966005 / 1000000000000) (42819967866 / 1000000000000)))) (orderedInterval (-1671208917 / 1000000000000) (-1671208713 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate311_chunkChecks3_1 :
    compactCertificate311.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1650218167394631 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38333960342 / 1000000000000) (-38333956322 / 1000000000000), orderedInterval (8626855380 / 1000000000000) (8626859400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (952753903166799 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10893740269 / 1000000000000) (10893740270 / 1000000000000), orderedInterval (50515119751 / 1000000000000) (50515119752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1690678520403291 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23803281564 / 1000000000000) (23803286321 / 1000000000000), orderedInterval (-30680918507 / 1000000000000) (-30680913751 / 1000000000000)))) (orderedInterval (61810843222 / 1000000000000) (61810860088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1579651182810279 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5713884378 / 1000000000000) (-5713884372 / 1000000000000), orderedInterval (39748954045 / 1000000000000) (39748954051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1127313620958807 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6160228260 / 1000000000000) (-6160228248 / 1000000000000), orderedInterval (47137847678 / 1000000000000) (47137847690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1278253495985553 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4192472063 / 1000000000000) (-4192472058 / 1000000000000), orderedInterval (44442812554 / 1000000000000) (44442812559 / 1000000000000)))) (orderedInterval (-7685959713 / 1000000000000) (-7685959607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1065674500326657 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8182361856 / 1000000000000) (-8182361855 / 1000000000000), orderedInterval (-48178001521 / 1000000000000) (-48178001520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (941555739703797 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27375176858 / 1000000000000) (-27375176857 / 1000000000000), orderedInterval (-44158890979 / 1000000000000) (-44158890978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (272899552263903 / 800000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21619748236 / 1000000000000) (21619749914 / 1000000000000), orderedInterval (-37432579535 / 1000000000000) (-37432577857 / 1000000000000)))) (orderedInterval (2507949743 / 1000000000000) (2507950075 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate311_chunkChecks3_2 :
    compactCertificate311.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (754854523478541 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48961788391 / 1000000000000) (48961788392 / 1000000000000), orderedInterval (31114607940 / 1000000000000) (31114607941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (639898539337701 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32326469132 / 1000000000000) (-32326469131 / 1000000000000), orderedInterval (-54070110940 / 1000000000000) (-54070110939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (400418794475703 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27934493903 / 1000000000000) (27934493904 / 1000000000000), orderedInterval (74554943253 / 1000000000000) (74554943254 / 1000000000000)))) (orderedInterval (2905487253 / 1000000000000) (2905487294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (215346559401801 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101840491138 / 1000000000000) (-101840491137 / 1000000000000), orderedInterval (-37174561173 / 1000000000000) (-37174561171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (584707799648403 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42177992190 / 1000000000000) (42178018415 / 1000000000000), orderedInterval (-50900084071 / 1000000000000) (-50900057846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (798368512212531 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35732465141 / 1000000000000) (-35732446289 / 1000000000000), orderedInterval (43825040255 / 1000000000000) (43825059107 / 1000000000000)))) (orderedInterval (3675666516 / 1000000000000) (3675668673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (337581205524297 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30287805748 / 1000000000000) (-30287805747 / 1000000000000), orderedInterval (-81221163389 / 1000000000000) (-81221163388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1372248858508137 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42546973222 / 1000000000000) (-42546973203 / 1000000000000), orderedInterval (-6679719641 / 1000000000000) (-6679719621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (916598641894983 / 4000000000000) 3 (IntervalRat.scale (369 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29685209516 / 1000000000000) (-29685209515 / 1000000000000), orderedInterval (-43489494019 / 1000000000000) (-43489494018 / 1000000000000)))) (orderedInterval (-18970005167 / 1000000000000) (-18970004992 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate311_chunkChecks3 :
    compactCertificate311.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate311.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate311_chunkChecks3_0
    compactCertificate311_chunkChecks3_1 compactCertificate311_chunkChecks3_2

theorem compactCertificate311_chunkChecks4_0 :
    compactCertificate311.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (369 / 2) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4064320814 / 1000000000000) (4064320824 / 1000000000000), orderedInterval (-58611419773 / 1000000000000) (-58611419763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (543607459775469 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-68417440866 / 1000000000000) (-68417440803 / 1000000000000), orderedInterval (2103753377 / 1000000000000) (2103753440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (175791483371277 / 800000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30953607678 / 1000000000000) (30953607679 / 1000000000000), orderedInterval (43964047120 / 1000000000000) (43964047121 / 1000000000000)))) (orderedInterval (4873191422 / 1000000000000) (4873191449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (158623300986183 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49645467601 / 1000000000000) (49645469920 / 1000000000000), orderedInterval (-117201309692 / 1000000000000) (-117201307374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (426084498661851 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36464528442 / 1000000000000) (36464528443 / 1000000000000), orderedInterval (67996574810 / 1000000000000) (67996574811 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1156902299105967 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39068304709 / 1000000000000) (39068304710 / 1000000000000), orderedInterval (25909081453 / 1000000000000) (25909081454 / 1000000000000)))) (orderedInterval (-16696534322 / 1000000000000) (-16696534240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (852168997324071 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10793765751 / 1000000000000) (10793765752 / 1000000000000), orderedInterval (53563236469 / 1000000000000) (53563236470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1460206101670083 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41233705467 / 1000000000000) (41233705489 / 1000000000000), orderedInterval (6553936356 / 1000000000000) (6553936378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1075581205524297 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23187951802 / 1000000000000) (-23187949940 / 1000000000000), orderedInterval (42819966005 / 1000000000000) (42819967866 / 1000000000000)))) (orderedInterval (-22002037119 / 1000000000000) (-22002036796 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate311_chunkChecks4_1 :
    compactCertificate311.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1650218167394631 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38333960342 / 1000000000000) (-38333956322 / 1000000000000), orderedInterval (8626855380 / 1000000000000) (8626859400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (952753903166799 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10893740269 / 1000000000000) (10893740270 / 1000000000000), orderedInterval (50515119751 / 1000000000000) (50515119752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1690678520403291 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23803281564 / 1000000000000) (23803286321 / 1000000000000), orderedInterval (-30680918507 / 1000000000000) (-30680913751 / 1000000000000)))) (orderedInterval (265058440805 / 1000000000000) (265058479044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1579651182810279 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5713884378 / 1000000000000) (-5713884372 / 1000000000000), orderedInterval (39748954045 / 1000000000000) (39748954051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1127313620958807 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6160228260 / 1000000000000) (-6160228248 / 1000000000000), orderedInterval (47137847678 / 1000000000000) (47137847690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1278253495985553 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4192472063 / 1000000000000) (-4192472058 / 1000000000000), orderedInterval (44442812554 / 1000000000000) (44442812559 / 1000000000000)))) (orderedInterval (-732038778 / 1000000000000) (-732038595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1065674500326657 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8182361856 / 1000000000000) (-8182361855 / 1000000000000), orderedInterval (-48178001521 / 1000000000000) (-48178001520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (941555739703797 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27375176858 / 1000000000000) (-27375176857 / 1000000000000), orderedInterval (-44158890979 / 1000000000000) (-44158890978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (272899552263903 / 800000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21619748236 / 1000000000000) (21619749914 / 1000000000000), orderedInterval (-37432579535 / 1000000000000) (-37432577857 / 1000000000000)))) (orderedInterval (10181301392 / 1000000000000) (10181301991 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate311_chunkChecks4_2 :
    compactCertificate311.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (754854523478541 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48961788391 / 1000000000000) (48961788392 / 1000000000000), orderedInterval (31114607940 / 1000000000000) (31114607941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (639898539337701 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32326469132 / 1000000000000) (-32326469131 / 1000000000000), orderedInterval (-54070110940 / 1000000000000) (-54070110939 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (400418794475703 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27934493903 / 1000000000000) (27934493904 / 1000000000000), orderedInterval (74554943253 / 1000000000000) (74554943254 / 1000000000000)))) (orderedInterval (-7486975254 / 1000000000000) (-7486975214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (215346559401801 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101840491138 / 1000000000000) (-101840491137 / 1000000000000), orderedInterval (-37174561173 / 1000000000000) (-37174561171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (584707799648403 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42177992190 / 1000000000000) (42178018415 / 1000000000000), orderedInterval (-50900084071 / 1000000000000) (-50900057846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (798368512212531 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35732465141 / 1000000000000) (-35732446289 / 1000000000000), orderedInterval (43825040255 / 1000000000000) (43825059107 / 1000000000000)))) (orderedInterval (3347258811 / 1000000000000) (3347261069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (337581205524297 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30287805748 / 1000000000000) (-30287805747 / 1000000000000), orderedInterval (-81221163389 / 1000000000000) (-81221163388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1372248858508137 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42546973222 / 1000000000000) (-42546973203 / 1000000000000), orderedInterval (-6679719641 / 1000000000000) (-6679719621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (916598641894983 / 4000000000000) 4 (IntervalRat.scale (369 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29685209516 / 1000000000000) (-29685209515 / 1000000000000), orderedInterval (-43489494019 / 1000000000000) (-43489494018 / 1000000000000)))) (orderedInterval (54851178248 / 1000000000000) (54851178530 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate311_chunkChecks4 :
    compactCertificate311.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate311.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate311_chunkChecks4_0
    compactCertificate311_chunkChecks4_1 compactCertificate311_chunkChecks4_2

theorem compactCertificate311_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate311.chunkCheck r b = true :=
  compactCertificate311.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate311_chunkChecks0
    · exact compactCertificate311_chunkChecks1
    · exact compactCertificate311_chunkChecks2
    · exact compactCertificate311_chunkChecks3
    · exact compactCertificate311_chunkChecks4)

theorem compactCertificate311_coefficient0 :
    compactCertificate311.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate311_coefficient1 :
    compactCertificate311.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate311_coefficient2 :
    compactCertificate311.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate311_coefficient3 :
    compactCertificate311.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate311_coefficient4 :
    compactCertificate311.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate311_coefficients : ∀ r : Fin 5,
    compactCertificate311.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate311_coefficient0
  · exact compactCertificate311_coefficient1
  · exact compactCertificate311_coefficient2
  · exact compactCertificate311_coefficient3
  · exact compactCertificate311_coefficient4

theorem compactCertificate311_lower : (1 : ℚ) ≤ compactCertificate311.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate311, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate311_proves {t : ℝ} (ht : t ∈ compactCertificate311.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate311.proves compactCertificate311_states compactCertificate311_chunks
    compactCertificate311_coefficients compactCertificate311_lower ht

end Erdos232
