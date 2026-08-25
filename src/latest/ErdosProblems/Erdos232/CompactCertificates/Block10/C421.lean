/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate421 : CompactCertificate where
  left := 292
  right := 293
  center := 585 / 2
  grid := fun i =>
    match i.val with
    | 0 => 93
    | 1 => 69
    | 2 => 111
    | 3 => 20
    | 4 => 54
    | 5 => 146
    | 6 => 108
    | 7 => 184
    | 8 => 136
    | 9 => 208
    | 10 => 120
    | 11 => 213
    | 12 => 199
    | 13 => 142
    | 14 => 161
    | 15 => 135
    | 16 => 119
    | 17 => 172
    | 18 => 95
    | 19 => 81
    | 20 => 51
    | 21 => 27
    | 22 => 74
    | 23 => 101
    | 24 => 43
    | 25 => 173
    | _ => 116
  point := fun i =>
    match i.val with
    | 0 => 585 / 2
    | 1 => 172363340904417 / 800000000000
    | 2 => 55738763020161 / 160000000000
    | 3 => 50295192995619 / 800000000000
    | 4 => 135099962990343 / 800000000000
    | 5 => 366822680204331 / 800000000000
    | 6 => 270199925980803 / 800000000000
    | 7 => 462992178578319 / 800000000000
    | 8 => 341037943215021 / 800000000000
    | 9 => 523239906734883 / 800000000000
    | 10 => 302092701004107 / 800000000000
    | 11 => 536068799152263 / 800000000000
    | 12 => 500865009183747 / 800000000000
    | 13 => 357440904206451 / 800000000000
    | 14 => 405299888971029 / 800000000000
    | 15 => 337896792786501 / 800000000000
    | 16 => 298542063808521 / 800000000000
    | 17 => 86529126327579 / 160000000000
    | 18 => 239344117200513 / 800000000000
    | 19 => 202894658814393 / 800000000000
    | 20 => 126962056784979 / 800000000000
    | 21 => 68280616395693 / 800000000000
    | 22 => 185395155986079 / 800000000000
    | 23 => 253141235579583 / 800000000000
    | 24 => 107037943215021 / 800000000000
    | 25 => 435103296600141 / 800000000000
    | _ => 290628837674019 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-41927966477 / 1000000000000) (-41927966476 / 1000000000000), orderedInterval (-20386127095 / 1000000000000) (-20386127094 / 1000000000000))
    | 1 => (orderedInterval (27521838380 / 1000000000000) (27521842040 / 1000000000000), orderedInterval (-46939584798 / 1000000000000) (-46939581137 / 1000000000000))
    | 2 => (orderedInterval (-18034973443 / 1000000000000) (-18034973442 / 1000000000000), orderedInterval (-38732075303 / 1000000000000) (-38732075302 / 1000000000000))
    | 3 => (orderedInterval (73610715717 / 1000000000000) (73610715718 / 1000000000000), orderedInterval (68026364123 / 1000000000000) (68026364124 / 1000000000000))
    | 4 => (orderedInterval (835508848 / 1000000000000) (835508852 / 1000000000000), orderedInterval (61390430308 / 1000000000000) (61390430312 / 1000000000000))
    | 5 => (orderedInterval (22280553106 / 1000000000000) (22280553107 / 1000000000000), orderedInterval (29841655343 / 1000000000000) (29841655344 / 1000000000000))
    | 6 => (orderedInterval (-29817399710 / 1000000000000) (-29817380456 / 1000000000000), orderedInterval (31600564183 / 1000000000000) (31600583437 / 1000000000000))
    | 7 => (orderedInterval (33005819603 / 1000000000000) (33005819852 / 1000000000000), orderedInterval (3231087568 / 1000000000000) (3231087817 / 1000000000000))
    | 8 => (orderedInterval (-6692747866 / 1000000000000) (-6692747859 / 1000000000000), orderedInterval (38068039629 / 1000000000000) (38068039636 / 1000000000000))
    | 9 => (orderedInterval (30654786063 / 1000000000000) (30654786189 / 1000000000000), orderedInterval (5776074772 / 1000000000000) (5776074897 / 1000000000000))
    | 10 => (orderedInterval (40528787228 / 1000000000000) (40528787252 / 1000000000000), orderedInterval (6527255389 / 1000000000000) (6527255412 / 1000000000000))
    | 11 => (orderedInterval (-30516326227 / 1000000000000) (-30516319333 / 1000000000000), orderedInterval (4359886154 / 1000000000000) (4359893048 / 1000000000000))
    | 12 => (orderedInterval (-31663330437 / 1000000000000) (-31663326118 / 1000000000000), orderedInterval (3802296808 / 1000000000000) (3802301127 / 1000000000000))
    | 13 => (orderedInterval (37591858916 / 1000000000000) (37591859027 / 1000000000000), orderedInterval (3377066309 / 1000000000000) (3377066421 / 1000000000000))
    | 14 => (orderedInterval (-35415944529 / 1000000000000) (-35415943602 / 1000000000000), orderedInterval (1551649500 / 1000000000000) (1551650427 / 1000000000000))
    | 15 => (orderedInterval (31779532829 / 1000000000000) (31779613012 / 1000000000000), orderedInterval (-22338128247 / 1000000000000) (-22338048064 / 1000000000000))
    | 16 => (orderedInterval (-4662127288 / 1000000000000) (-4662127287 / 1000000000000), orderedInterval (-41032872738 / 1000000000000) (-41032872737 / 1000000000000))
    | 17 => (orderedInterval (32430380348 / 1000000000000) (32430380354 / 1000000000000), orderedInterval (11169848982 / 1000000000000) (11169848989 / 1000000000000))
    | 18 => (orderedInterval (-46054087752 / 1000000000000) (-46054087690 / 1000000000000), orderedInterval (-2549652379 / 1000000000000) (-2549652317 / 1000000000000))
    | 19 => (orderedInterval (3293095934 / 1000000000000) (3293095940 / 1000000000000), orderedInterval (-49999584931 / 1000000000000) (-49999584926 / 1000000000000))
    | 20 => (orderedInterval (42426989024 / 1000000000000) (42427024948 / 1000000000000), orderedInterval (-47158707409 / 1000000000000) (-47158671485 / 1000000000000))
    | 21 => (orderedInterval (-83481364651 / 1000000000000) (-83481364650 / 1000000000000), orderedInterval (-21638200113 / 1000000000000) (-21638200112 / 1000000000000))
    | 22 => (orderedInterval (2669128390 / 1000000000000) (2669128392 / 1000000000000), orderedInterval (52338914054 / 1000000000000) (52338914056 / 1000000000000))
    | 23 => (orderedInterval (4000625633 / 1000000000000) (4000625638 / 1000000000000), orderedInterval (-44681832550 / 1000000000000) (-44681832545 / 1000000000000))
    | 24 => (orderedInterval (33468391944 / 1000000000000) (33468396323 / 1000000000000), orderedInterval (-60440665675 / 1000000000000) (-60440661296 / 1000000000000))
    | 25 => (orderedInterval (-31484891693 / 1000000000000) (-31484891691 / 1000000000000), orderedInterval (-13358298479 / 1000000000000) (-13358298477 / 1000000000000))
    | _ => (orderedInterval (-14497543474 / 1000000000000) (-14497543299 / 1000000000000), orderedInterval (39290999480 / 1000000000000) (39290999655 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17420640810 / 1000000000000) (-17420640754 / 1000000000000)
      | 1 => orderedInterval (-2352034728 / 1000000000000) (-2352034692 / 1000000000000)
      | 2 => orderedInterval (-1179782060 / 1000000000000) (-1179782035 / 1000000000000)
      | 3 => orderedInterval (-6782211391 / 1000000000000) (-6782210271 / 1000000000000)
      | 4 => orderedInterval (4305639723 / 1000000000000) (4305639852 / 1000000000000)
      | 5 => orderedInterval (1464123433 / 1000000000000) (1464124388 / 1000000000000)
      | 6 => orderedInterval (8558533548 / 1000000000000) (8558534802 / 1000000000000)
      | 7 => orderedInterval (1174335572 / 1000000000000) (1174335608 / 1000000000000)
      | _ => orderedInterval (5484808235 / 1000000000000) (5484808376 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11109477009 / 1000000000000) (-11109476959 / 1000000000000)
      | 1 => orderedInterval (-2190113597 / 1000000000000) (-2190113557 / 1000000000000)
      | 2 => orderedInterval (1143689247 / 1000000000000) (1143689291 / 1000000000000)
      | 3 => orderedInterval (-250760656 / 1000000000000) (-250758118 / 1000000000000)
      | 4 => orderedInterval (327279734 / 1000000000000) (327279983 / 1000000000000)
      | 5 => orderedInterval (3152139692 / 1000000000000) (3152141071 / 1000000000000)
      | 6 => orderedInterval (2037776810 / 1000000000000) (2037777523 / 1000000000000)
      | 7 => orderedInterval (2880300871 / 1000000000000) (2880300904 / 1000000000000)
      | _ => orderedInterval (-7300850101 / 1000000000000) (-7300849933 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (18018810939 / 1000000000000) (18018810985 / 1000000000000)
      | 1 => orderedInterval (3926572978 / 1000000000000) (3926573034 / 1000000000000)
      | 2 => orderedInterval (4325108217 / 1000000000000) (4325108299 / 1000000000000)
      | 3 => orderedInterval (44998063527 / 1000000000000) (44998069308 / 1000000000000)
      | 4 => orderedInterval (-11452206112 / 1000000000000) (-11452205622 / 1000000000000)
      | 5 => orderedInterval (-4048776467 / 1000000000000) (-4048774470 / 1000000000000)
      | 6 => orderedInterval (-7977336333 / 1000000000000) (-7977335910 / 1000000000000)
      | 7 => orderedInterval (255727533 / 1000000000000) (255727565 / 1000000000000)
      | _ => orderedInterval (-13074375185 / 1000000000000) (-13074374960 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (12033175583 / 1000000000000) (12033175628 / 1000000000000)
      | 1 => orderedInterval (7734918124 / 1000000000000) (7734918208 / 1000000000000)
      | 2 => orderedInterval (-2090962817 / 1000000000000) (-2090962664 / 1000000000000)
      | 3 => orderedInterval (2828708226 / 1000000000000) (2828721407 / 1000000000000)
      | 4 => orderedInterval (-385109677 / 1000000000000) (-385108690 / 1000000000000)
      | 5 => orderedInterval (-5893444719 / 1000000000000) (-5893441830 / 1000000000000)
      | 6 => orderedInterval (-2008515967 / 1000000000000) (-2008515705 / 1000000000000)
      | 7 => orderedInterval (-3755551420 / 1000000000000) (-3755551387 / 1000000000000)
      | _ => orderedInterval (7212824277 / 1000000000000) (7212824603 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18754763271 / 1000000000000) (-18754763224 / 1000000000000)
      | 1 => orderedInterval (-9616346815 / 1000000000000) (-9616346687 / 1000000000000)
      | 2 => orderedInterval (-16317870632 / 1000000000000) (-16317870342 / 1000000000000)
      | 3 => orderedInterval (-247337868044 / 1000000000000) (-247337837898 / 1000000000000)
      | 4 => orderedInterval (32967913098 / 1000000000000) (32967915116 / 1000000000000)
      | 5 => orderedInterval (12046109271 / 1000000000000) (12046113465 / 1000000000000)
      | 6 => orderedInterval (8087779235 / 1000000000000) (8087779411 / 1000000000000)
      | 7 => orderedInterval (-406921476 / 1000000000000) (-406921441 / 1000000000000)
      | _ => orderedInterval (37068693102 / 1000000000000) (37068693600 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-6747228478 / 1000000000000) (-6747224726 / 1000000000000)
    | 1 => orderedInterval (-11310015009 / 1000000000000) (-11310009795 / 1000000000000)
    | 2 => orderedInterval (34971589097 / 1000000000000) (34971598229 / 1000000000000)
    | 3 => orderedInterval (15676041610 / 1000000000000) (15676059570 / 1000000000000)
    | _ => orderedInterval (-202263275532 / 1000000000000) (-202263238000 / 1000000000000)

theorem compactCertificate421_stateChecks0 :
    compactCertificate421.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (585 / 2)) (orderedInterval (-41927966477 / 1000000000000) (-41927966476 / 1000000000000), orderedInterval (-20386127095 / 1000000000000) (-20386127094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (172363340904417 / 800000000000)) (orderedInterval (27521838380 / 1000000000000) (27521842040 / 1000000000000), orderedInterval (-46939584798 / 1000000000000) (-46939581137 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (55738763020161 / 160000000000)) (orderedInterval (-18034973443 / 1000000000000) (-18034973442 / 1000000000000), orderedInterval (-38732075303 / 1000000000000) (-38732075302 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_stateChecks1 :
    compactCertificate421.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (50295192995619 / 800000000000)) (orderedInterval (73610715717 / 1000000000000) (73610715718 / 1000000000000), orderedInterval (68026364123 / 1000000000000) (68026364124 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (135099962990343 / 800000000000)) (orderedInterval (835508848 / 1000000000000) (835508852 / 1000000000000), orderedInterval (61390430308 / 1000000000000) (61390430312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (366822680204331 / 800000000000)) (orderedInterval (22280553106 / 1000000000000) (22280553107 / 1000000000000), orderedInterval (29841655343 / 1000000000000) (29841655344 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_stateChecks2 :
    compactCertificate421.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (270199925980803 / 800000000000)) (orderedInterval (-29817399710 / 1000000000000) (-29817380456 / 1000000000000), orderedInterval (31600564183 / 1000000000000) (31600583437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (462992178578319 / 800000000000)) (orderedInterval (33005819603 / 1000000000000) (33005819852 / 1000000000000), orderedInterval (3231087568 / 1000000000000) (3231087817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (341037943215021 / 800000000000)) (orderedInterval (-6692747866 / 1000000000000) (-6692747859 / 1000000000000), orderedInterval (38068039629 / 1000000000000) (38068039636 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_stateChecks3 :
    compactCertificate421.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (523239906734883 / 800000000000)) (orderedInterval (30654786063 / 1000000000000) (30654786189 / 1000000000000), orderedInterval (5776074772 / 1000000000000) (5776074897 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (302092701004107 / 800000000000)) (orderedInterval (40528787228 / 1000000000000) (40528787252 / 1000000000000), orderedInterval (6527255389 / 1000000000000) (6527255412 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (536068799152263 / 800000000000)) (orderedInterval (-30516326227 / 1000000000000) (-30516319333 / 1000000000000), orderedInterval (4359886154 / 1000000000000) (4359893048 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_stateChecks4 :
    compactCertificate421.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (500865009183747 / 800000000000)) (orderedInterval (-31663330437 / 1000000000000) (-31663326118 / 1000000000000), orderedInterval (3802296808 / 1000000000000) (3802301127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (357440904206451 / 800000000000)) (orderedInterval (37591858916 / 1000000000000) (37591859027 / 1000000000000), orderedInterval (3377066309 / 1000000000000) (3377066421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (405299888971029 / 800000000000)) (orderedInterval (-35415944529 / 1000000000000) (-35415943602 / 1000000000000), orderedInterval (1551649500 / 1000000000000) (1551650427 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_stateChecks5 :
    compactCertificate421.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (337896792786501 / 800000000000)) (orderedInterval (31779532829 / 1000000000000) (31779613012 / 1000000000000), orderedInterval (-22338128247 / 1000000000000) (-22338048064 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (298542063808521 / 800000000000)) (orderedInterval (-4662127288 / 1000000000000) (-4662127287 / 1000000000000), orderedInterval (-41032872738 / 1000000000000) (-41032872737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (86529126327579 / 160000000000)) (orderedInterval (32430380348 / 1000000000000) (32430380354 / 1000000000000), orderedInterval (11169848982 / 1000000000000) (11169848989 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_stateChecks6 :
    compactCertificate421.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (239344117200513 / 800000000000)) (orderedInterval (-46054087752 / 1000000000000) (-46054087690 / 1000000000000), orderedInterval (-2549652379 / 1000000000000) (-2549652317 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (202894658814393 / 800000000000)) (orderedInterval (3293095934 / 1000000000000) (3293095940 / 1000000000000), orderedInterval (-49999584931 / 1000000000000) (-49999584926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (126962056784979 / 800000000000)) (orderedInterval (42426989024 / 1000000000000) (42427024948 / 1000000000000), orderedInterval (-47158707409 / 1000000000000) (-47158671485 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_stateChecks7 :
    compactCertificate421.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (68280616395693 / 800000000000)) (orderedInterval (-83481364651 / 1000000000000) (-83481364650 / 1000000000000), orderedInterval (-21638200113 / 1000000000000) (-21638200112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (185395155986079 / 800000000000)) (orderedInterval (2669128390 / 1000000000000) (2669128392 / 1000000000000), orderedInterval (52338914054 / 1000000000000) (52338914056 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (253141235579583 / 800000000000)) (orderedInterval (4000625633 / 1000000000000) (4000625638 / 1000000000000), orderedInterval (-44681832550 / 1000000000000) (-44681832545 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_stateChecks8 :
    compactCertificate421.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (107037943215021 / 800000000000)) (orderedInterval (33468391944 / 1000000000000) (33468396323 / 1000000000000), orderedInterval (-60440665675 / 1000000000000) (-60440661296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (435103296600141 / 800000000000)) (orderedInterval (-31484891693 / 1000000000000) (-31484891691 / 1000000000000), orderedInterval (-13358298479 / 1000000000000) (-13358298477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (290628837674019 / 800000000000)) (orderedInterval (-14497543474 / 1000000000000) (-14497543299 / 1000000000000), orderedInterval (39290999480 / 1000000000000) (39290999655 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_states : ∀ j,
    BesselStateValid (compactCertificate421.point j) (compactCertificate421.state j) :=
  compactCertificate421.statesValid_of_checks3 compactCertificate421_stateChecks0
    compactCertificate421_stateChecks1 compactCertificate421_stateChecks2
    compactCertificate421_stateChecks3 compactCertificate421_stateChecks4
    compactCertificate421_stateChecks5 compactCertificate421_stateChecks6
    compactCertificate421_stateChecks7 compactCertificate421_stateChecks8

theorem compactCertificate421_chunkChecks0_0 :
    compactCertificate421.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (585 / 2) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41927966477 / 1000000000000) (-41927966476 / 1000000000000), orderedInterval (-20386127095 / 1000000000000) (-20386127094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (172363340904417 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27521838380 / 1000000000000) (27521842040 / 1000000000000), orderedInterval (-46939584798 / 1000000000000) (-46939581137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (55738763020161 / 160000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18034973443 / 1000000000000) (-18034973442 / 1000000000000), orderedInterval (-38732075303 / 1000000000000) (-38732075302 / 1000000000000)))) (orderedInterval (-17420640810 / 1000000000000) (-17420640754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (50295192995619 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73610715717 / 1000000000000) (73610715718 / 1000000000000), orderedInterval (68026364123 / 1000000000000) (68026364124 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (135099962990343 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (835508848 / 1000000000000) (835508852 / 1000000000000), orderedInterval (61390430308 / 1000000000000) (61390430312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (366822680204331 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22280553106 / 1000000000000) (22280553107 / 1000000000000), orderedInterval (29841655343 / 1000000000000) (29841655344 / 1000000000000)))) (orderedInterval (-2352034728 / 1000000000000) (-2352034692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (270199925980803 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29817399710 / 1000000000000) (-29817380456 / 1000000000000), orderedInterval (31600564183 / 1000000000000) (31600583437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (462992178578319 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33005819603 / 1000000000000) (33005819852 / 1000000000000), orderedInterval (3231087568 / 1000000000000) (3231087817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (341037943215021 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6692747866 / 1000000000000) (-6692747859 / 1000000000000), orderedInterval (38068039629 / 1000000000000) (38068039636 / 1000000000000)))) (orderedInterval (-1179782060 / 1000000000000) (-1179782035 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks0_1 :
    compactCertificate421.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (523239906734883 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30654786063 / 1000000000000) (30654786189 / 1000000000000), orderedInterval (5776074772 / 1000000000000) (5776074897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (302092701004107 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40528787228 / 1000000000000) (40528787252 / 1000000000000), orderedInterval (6527255389 / 1000000000000) (6527255412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (536068799152263 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30516326227 / 1000000000000) (-30516319333 / 1000000000000), orderedInterval (4359886154 / 1000000000000) (4359893048 / 1000000000000)))) (orderedInterval (-6782211391 / 1000000000000) (-6782210271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (500865009183747 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31663330437 / 1000000000000) (-31663326118 / 1000000000000), orderedInterval (3802296808 / 1000000000000) (3802301127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (357440904206451 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37591858916 / 1000000000000) (37591859027 / 1000000000000), orderedInterval (3377066309 / 1000000000000) (3377066421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (405299888971029 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35415944529 / 1000000000000) (-35415943602 / 1000000000000), orderedInterval (1551649500 / 1000000000000) (1551650427 / 1000000000000)))) (orderedInterval (4305639723 / 1000000000000) (4305639852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (337896792786501 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31779532829 / 1000000000000) (31779613012 / 1000000000000), orderedInterval (-22338128247 / 1000000000000) (-22338048064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (298542063808521 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4662127288 / 1000000000000) (-4662127287 / 1000000000000), orderedInterval (-41032872738 / 1000000000000) (-41032872737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (86529126327579 / 160000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32430380348 / 1000000000000) (32430380354 / 1000000000000), orderedInterval (11169848982 / 1000000000000) (11169848989 / 1000000000000)))) (orderedInterval (1464123433 / 1000000000000) (1464124388 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks0_2 :
    compactCertificate421.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (239344117200513 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46054087752 / 1000000000000) (-46054087690 / 1000000000000), orderedInterval (-2549652379 / 1000000000000) (-2549652317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (202894658814393 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3293095934 / 1000000000000) (3293095940 / 1000000000000), orderedInterval (-49999584931 / 1000000000000) (-49999584926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (126962056784979 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42426989024 / 1000000000000) (42427024948 / 1000000000000), orderedInterval (-47158707409 / 1000000000000) (-47158671485 / 1000000000000)))) (orderedInterval (8558533548 / 1000000000000) (8558534802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (68280616395693 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-83481364651 / 1000000000000) (-83481364650 / 1000000000000), orderedInterval (-21638200113 / 1000000000000) (-21638200112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (185395155986079 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2669128390 / 1000000000000) (2669128392 / 1000000000000), orderedInterval (52338914054 / 1000000000000) (52338914056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (253141235579583 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4000625633 / 1000000000000) (4000625638 / 1000000000000), orderedInterval (-44681832550 / 1000000000000) (-44681832545 / 1000000000000)))) (orderedInterval (1174335572 / 1000000000000) (1174335608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (107037943215021 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33468391944 / 1000000000000) (33468396323 / 1000000000000), orderedInterval (-60440665675 / 1000000000000) (-60440661296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (435103296600141 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31484891693 / 1000000000000) (-31484891691 / 1000000000000), orderedInterval (-13358298479 / 1000000000000) (-13358298477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (290628837674019 / 800000000000) 0 (IntervalRat.scale (585 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14497543474 / 1000000000000) (-14497543299 / 1000000000000), orderedInterval (39290999480 / 1000000000000) (39290999655 / 1000000000000)))) (orderedInterval (5484808235 / 1000000000000) (5484808376 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks0 :
    compactCertificate421.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate421.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate421_chunkChecks0_0
    compactCertificate421_chunkChecks0_1 compactCertificate421_chunkChecks0_2

theorem compactCertificate421_chunkChecks1_0 :
    compactCertificate421.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (585 / 2) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41927966477 / 1000000000000) (-41927966476 / 1000000000000), orderedInterval (-20386127095 / 1000000000000) (-20386127094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (172363340904417 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27521838380 / 1000000000000) (27521842040 / 1000000000000), orderedInterval (-46939584798 / 1000000000000) (-46939581137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (55738763020161 / 160000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18034973443 / 1000000000000) (-18034973442 / 1000000000000), orderedInterval (-38732075303 / 1000000000000) (-38732075302 / 1000000000000)))) (orderedInterval (-11109477009 / 1000000000000) (-11109476959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (50295192995619 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73610715717 / 1000000000000) (73610715718 / 1000000000000), orderedInterval (68026364123 / 1000000000000) (68026364124 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (135099962990343 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (835508848 / 1000000000000) (835508852 / 1000000000000), orderedInterval (61390430308 / 1000000000000) (61390430312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (366822680204331 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22280553106 / 1000000000000) (22280553107 / 1000000000000), orderedInterval (29841655343 / 1000000000000) (29841655344 / 1000000000000)))) (orderedInterval (-2190113597 / 1000000000000) (-2190113557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (270199925980803 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29817399710 / 1000000000000) (-29817380456 / 1000000000000), orderedInterval (31600564183 / 1000000000000) (31600583437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (462992178578319 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33005819603 / 1000000000000) (33005819852 / 1000000000000), orderedInterval (3231087568 / 1000000000000) (3231087817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (341037943215021 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6692747866 / 1000000000000) (-6692747859 / 1000000000000), orderedInterval (38068039629 / 1000000000000) (38068039636 / 1000000000000)))) (orderedInterval (1143689247 / 1000000000000) (1143689291 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks1_1 :
    compactCertificate421.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (523239906734883 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30654786063 / 1000000000000) (30654786189 / 1000000000000), orderedInterval (5776074772 / 1000000000000) (5776074897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (302092701004107 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40528787228 / 1000000000000) (40528787252 / 1000000000000), orderedInterval (6527255389 / 1000000000000) (6527255412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (536068799152263 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30516326227 / 1000000000000) (-30516319333 / 1000000000000), orderedInterval (4359886154 / 1000000000000) (4359893048 / 1000000000000)))) (orderedInterval (-250760656 / 1000000000000) (-250758118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (500865009183747 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31663330437 / 1000000000000) (-31663326118 / 1000000000000), orderedInterval (3802296808 / 1000000000000) (3802301127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (357440904206451 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37591858916 / 1000000000000) (37591859027 / 1000000000000), orderedInterval (3377066309 / 1000000000000) (3377066421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (405299888971029 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35415944529 / 1000000000000) (-35415943602 / 1000000000000), orderedInterval (1551649500 / 1000000000000) (1551650427 / 1000000000000)))) (orderedInterval (327279734 / 1000000000000) (327279983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (337896792786501 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31779532829 / 1000000000000) (31779613012 / 1000000000000), orderedInterval (-22338128247 / 1000000000000) (-22338048064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (298542063808521 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4662127288 / 1000000000000) (-4662127287 / 1000000000000), orderedInterval (-41032872738 / 1000000000000) (-41032872737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (86529126327579 / 160000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32430380348 / 1000000000000) (32430380354 / 1000000000000), orderedInterval (11169848982 / 1000000000000) (11169848989 / 1000000000000)))) (orderedInterval (3152139692 / 1000000000000) (3152141071 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks1_2 :
    compactCertificate421.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (239344117200513 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46054087752 / 1000000000000) (-46054087690 / 1000000000000), orderedInterval (-2549652379 / 1000000000000) (-2549652317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (202894658814393 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3293095934 / 1000000000000) (3293095940 / 1000000000000), orderedInterval (-49999584931 / 1000000000000) (-49999584926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (126962056784979 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42426989024 / 1000000000000) (42427024948 / 1000000000000), orderedInterval (-47158707409 / 1000000000000) (-47158671485 / 1000000000000)))) (orderedInterval (2037776810 / 1000000000000) (2037777523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (68280616395693 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-83481364651 / 1000000000000) (-83481364650 / 1000000000000), orderedInterval (-21638200113 / 1000000000000) (-21638200112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (185395155986079 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2669128390 / 1000000000000) (2669128392 / 1000000000000), orderedInterval (52338914054 / 1000000000000) (52338914056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (253141235579583 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4000625633 / 1000000000000) (4000625638 / 1000000000000), orderedInterval (-44681832550 / 1000000000000) (-44681832545 / 1000000000000)))) (orderedInterval (2880300871 / 1000000000000) (2880300904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (107037943215021 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33468391944 / 1000000000000) (33468396323 / 1000000000000), orderedInterval (-60440665675 / 1000000000000) (-60440661296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (435103296600141 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31484891693 / 1000000000000) (-31484891691 / 1000000000000), orderedInterval (-13358298479 / 1000000000000) (-13358298477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (290628837674019 / 800000000000) 1 (IntervalRat.scale (585 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14497543474 / 1000000000000) (-14497543299 / 1000000000000), orderedInterval (39290999480 / 1000000000000) (39290999655 / 1000000000000)))) (orderedInterval (-7300850101 / 1000000000000) (-7300849933 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks1 :
    compactCertificate421.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate421.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate421_chunkChecks1_0
    compactCertificate421_chunkChecks1_1 compactCertificate421_chunkChecks1_2

theorem compactCertificate421_chunkChecks2_0 :
    compactCertificate421.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (585 / 2) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41927966477 / 1000000000000) (-41927966476 / 1000000000000), orderedInterval (-20386127095 / 1000000000000) (-20386127094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (172363340904417 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27521838380 / 1000000000000) (27521842040 / 1000000000000), orderedInterval (-46939584798 / 1000000000000) (-46939581137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (55738763020161 / 160000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18034973443 / 1000000000000) (-18034973442 / 1000000000000), orderedInterval (-38732075303 / 1000000000000) (-38732075302 / 1000000000000)))) (orderedInterval (18018810939 / 1000000000000) (18018810985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (50295192995619 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73610715717 / 1000000000000) (73610715718 / 1000000000000), orderedInterval (68026364123 / 1000000000000) (68026364124 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (135099962990343 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (835508848 / 1000000000000) (835508852 / 1000000000000), orderedInterval (61390430308 / 1000000000000) (61390430312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (366822680204331 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22280553106 / 1000000000000) (22280553107 / 1000000000000), orderedInterval (29841655343 / 1000000000000) (29841655344 / 1000000000000)))) (orderedInterval (3926572978 / 1000000000000) (3926573034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (270199925980803 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29817399710 / 1000000000000) (-29817380456 / 1000000000000), orderedInterval (31600564183 / 1000000000000) (31600583437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (462992178578319 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33005819603 / 1000000000000) (33005819852 / 1000000000000), orderedInterval (3231087568 / 1000000000000) (3231087817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (341037943215021 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6692747866 / 1000000000000) (-6692747859 / 1000000000000), orderedInterval (38068039629 / 1000000000000) (38068039636 / 1000000000000)))) (orderedInterval (4325108217 / 1000000000000) (4325108299 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks2_1 :
    compactCertificate421.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (523239906734883 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30654786063 / 1000000000000) (30654786189 / 1000000000000), orderedInterval (5776074772 / 1000000000000) (5776074897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (302092701004107 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40528787228 / 1000000000000) (40528787252 / 1000000000000), orderedInterval (6527255389 / 1000000000000) (6527255412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (536068799152263 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30516326227 / 1000000000000) (-30516319333 / 1000000000000), orderedInterval (4359886154 / 1000000000000) (4359893048 / 1000000000000)))) (orderedInterval (44998063527 / 1000000000000) (44998069308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (500865009183747 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31663330437 / 1000000000000) (-31663326118 / 1000000000000), orderedInterval (3802296808 / 1000000000000) (3802301127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (357440904206451 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37591858916 / 1000000000000) (37591859027 / 1000000000000), orderedInterval (3377066309 / 1000000000000) (3377066421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (405299888971029 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35415944529 / 1000000000000) (-35415943602 / 1000000000000), orderedInterval (1551649500 / 1000000000000) (1551650427 / 1000000000000)))) (orderedInterval (-11452206112 / 1000000000000) (-11452205622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (337896792786501 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31779532829 / 1000000000000) (31779613012 / 1000000000000), orderedInterval (-22338128247 / 1000000000000) (-22338048064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (298542063808521 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4662127288 / 1000000000000) (-4662127287 / 1000000000000), orderedInterval (-41032872738 / 1000000000000) (-41032872737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (86529126327579 / 160000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32430380348 / 1000000000000) (32430380354 / 1000000000000), orderedInterval (11169848982 / 1000000000000) (11169848989 / 1000000000000)))) (orderedInterval (-4048776467 / 1000000000000) (-4048774470 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks2_2 :
    compactCertificate421.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (239344117200513 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46054087752 / 1000000000000) (-46054087690 / 1000000000000), orderedInterval (-2549652379 / 1000000000000) (-2549652317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (202894658814393 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3293095934 / 1000000000000) (3293095940 / 1000000000000), orderedInterval (-49999584931 / 1000000000000) (-49999584926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (126962056784979 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42426989024 / 1000000000000) (42427024948 / 1000000000000), orderedInterval (-47158707409 / 1000000000000) (-47158671485 / 1000000000000)))) (orderedInterval (-7977336333 / 1000000000000) (-7977335910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (68280616395693 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-83481364651 / 1000000000000) (-83481364650 / 1000000000000), orderedInterval (-21638200113 / 1000000000000) (-21638200112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (185395155986079 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2669128390 / 1000000000000) (2669128392 / 1000000000000), orderedInterval (52338914054 / 1000000000000) (52338914056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (253141235579583 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4000625633 / 1000000000000) (4000625638 / 1000000000000), orderedInterval (-44681832550 / 1000000000000) (-44681832545 / 1000000000000)))) (orderedInterval (255727533 / 1000000000000) (255727565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (107037943215021 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33468391944 / 1000000000000) (33468396323 / 1000000000000), orderedInterval (-60440665675 / 1000000000000) (-60440661296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (435103296600141 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31484891693 / 1000000000000) (-31484891691 / 1000000000000), orderedInterval (-13358298479 / 1000000000000) (-13358298477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (290628837674019 / 800000000000) 2 (IntervalRat.scale (585 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14497543474 / 1000000000000) (-14497543299 / 1000000000000), orderedInterval (39290999480 / 1000000000000) (39290999655 / 1000000000000)))) (orderedInterval (-13074375185 / 1000000000000) (-13074374960 / 1000000000000))) = true
  rfl'

theorem compactCertificate421_chunkChecks2 :
    compactCertificate421.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate421.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate421_chunkChecks2_0
    compactCertificate421_chunkChecks2_1 compactCertificate421_chunkChecks2_2

theorem compactCertificate421_chunkChecks3_0 :
    compactCertificate421.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (585 / 2) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41927966477 / 1000000000000) (-41927966476 / 1000000000000), orderedInterval (-20386127095 / 1000000000000) (-20386127094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (172363340904417 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27521838380 / 1000000000000) (27521842040 / 1000000000000), orderedInterval (-46939584798 / 1000000000000) (-46939581137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (55738763020161 / 160000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18034973443 / 1000000000000) (-18034973442 / 1000000000000), orderedInterval (-38732075303 / 1000000000000) (-38732075302 / 1000000000000)))) (orderedInterval (12033175583 / 1000000000000) (12033175628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (50295192995619 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73610715717 / 1000000000000) (73610715718 / 1000000000000), orderedInterval (68026364123 / 1000000000000) (68026364124 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (135099962990343 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (835508848 / 1000000000000) (835508852 / 1000000000000), orderedInterval (61390430308 / 1000000000000) (61390430312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (366822680204331 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22280553106 / 1000000000000) (22280553107 / 1000000000000), orderedInterval (29841655343 / 1000000000000) (29841655344 / 1000000000000)))) (orderedInterval (7734918124 / 1000000000000) (7734918208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (270199925980803 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29817399710 / 1000000000000) (-29817380456 / 1000000000000), orderedInterval (31600564183 / 1000000000000) (31600583437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (462992178578319 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33005819603 / 1000000000000) (33005819852 / 1000000000000), orderedInterval (3231087568 / 1000000000000) (3231087817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (341037943215021 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6692747866 / 1000000000000) (-6692747859 / 1000000000000), orderedInterval (38068039629 / 1000000000000) (38068039636 / 1000000000000)))) (orderedInterval (-2090962817 / 1000000000000) (-2090962664 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate421_chunkChecks3_1 :
    compactCertificate421.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (523239906734883 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30654786063 / 1000000000000) (30654786189 / 1000000000000), orderedInterval (5776074772 / 1000000000000) (5776074897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (302092701004107 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40528787228 / 1000000000000) (40528787252 / 1000000000000), orderedInterval (6527255389 / 1000000000000) (6527255412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (536068799152263 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30516326227 / 1000000000000) (-30516319333 / 1000000000000), orderedInterval (4359886154 / 1000000000000) (4359893048 / 1000000000000)))) (orderedInterval (2828708226 / 1000000000000) (2828721407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (500865009183747 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31663330437 / 1000000000000) (-31663326118 / 1000000000000), orderedInterval (3802296808 / 1000000000000) (3802301127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (357440904206451 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37591858916 / 1000000000000) (37591859027 / 1000000000000), orderedInterval (3377066309 / 1000000000000) (3377066421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (405299888971029 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35415944529 / 1000000000000) (-35415943602 / 1000000000000), orderedInterval (1551649500 / 1000000000000) (1551650427 / 1000000000000)))) (orderedInterval (-385109677 / 1000000000000) (-385108690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (337896792786501 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31779532829 / 1000000000000) (31779613012 / 1000000000000), orderedInterval (-22338128247 / 1000000000000) (-22338048064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (298542063808521 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4662127288 / 1000000000000) (-4662127287 / 1000000000000), orderedInterval (-41032872738 / 1000000000000) (-41032872737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (86529126327579 / 160000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32430380348 / 1000000000000) (32430380354 / 1000000000000), orderedInterval (11169848982 / 1000000000000) (11169848989 / 1000000000000)))) (orderedInterval (-5893444719 / 1000000000000) (-5893441830 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate421_chunkChecks3_2 :
    compactCertificate421.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (239344117200513 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46054087752 / 1000000000000) (-46054087690 / 1000000000000), orderedInterval (-2549652379 / 1000000000000) (-2549652317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (202894658814393 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3293095934 / 1000000000000) (3293095940 / 1000000000000), orderedInterval (-49999584931 / 1000000000000) (-49999584926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (126962056784979 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42426989024 / 1000000000000) (42427024948 / 1000000000000), orderedInterval (-47158707409 / 1000000000000) (-47158671485 / 1000000000000)))) (orderedInterval (-2008515967 / 1000000000000) (-2008515705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (68280616395693 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-83481364651 / 1000000000000) (-83481364650 / 1000000000000), orderedInterval (-21638200113 / 1000000000000) (-21638200112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (185395155986079 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2669128390 / 1000000000000) (2669128392 / 1000000000000), orderedInterval (52338914054 / 1000000000000) (52338914056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (253141235579583 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4000625633 / 1000000000000) (4000625638 / 1000000000000), orderedInterval (-44681832550 / 1000000000000) (-44681832545 / 1000000000000)))) (orderedInterval (-3755551420 / 1000000000000) (-3755551387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (107037943215021 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33468391944 / 1000000000000) (33468396323 / 1000000000000), orderedInterval (-60440665675 / 1000000000000) (-60440661296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (435103296600141 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31484891693 / 1000000000000) (-31484891691 / 1000000000000), orderedInterval (-13358298479 / 1000000000000) (-13358298477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (290628837674019 / 800000000000) 3 (IntervalRat.scale (585 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14497543474 / 1000000000000) (-14497543299 / 1000000000000), orderedInterval (39290999480 / 1000000000000) (39290999655 / 1000000000000)))) (orderedInterval (7212824277 / 1000000000000) (7212824603 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate421_chunkChecks3 :
    compactCertificate421.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate421.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate421_chunkChecks3_0
    compactCertificate421_chunkChecks3_1 compactCertificate421_chunkChecks3_2

theorem compactCertificate421_chunkChecks4_0 :
    compactCertificate421.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (585 / 2) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41927966477 / 1000000000000) (-41927966476 / 1000000000000), orderedInterval (-20386127095 / 1000000000000) (-20386127094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (172363340904417 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27521838380 / 1000000000000) (27521842040 / 1000000000000), orderedInterval (-46939584798 / 1000000000000) (-46939581137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (55738763020161 / 160000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18034973443 / 1000000000000) (-18034973442 / 1000000000000), orderedInterval (-38732075303 / 1000000000000) (-38732075302 / 1000000000000)))) (orderedInterval (-18754763271 / 1000000000000) (-18754763224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (50295192995619 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73610715717 / 1000000000000) (73610715718 / 1000000000000), orderedInterval (68026364123 / 1000000000000) (68026364124 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (135099962990343 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (835508848 / 1000000000000) (835508852 / 1000000000000), orderedInterval (61390430308 / 1000000000000) (61390430312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (366822680204331 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (22280553106 / 1000000000000) (22280553107 / 1000000000000), orderedInterval (29841655343 / 1000000000000) (29841655344 / 1000000000000)))) (orderedInterval (-9616346815 / 1000000000000) (-9616346687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (270199925980803 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29817399710 / 1000000000000) (-29817380456 / 1000000000000), orderedInterval (31600564183 / 1000000000000) (31600583437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (462992178578319 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33005819603 / 1000000000000) (33005819852 / 1000000000000), orderedInterval (3231087568 / 1000000000000) (3231087817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (341037943215021 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6692747866 / 1000000000000) (-6692747859 / 1000000000000), orderedInterval (38068039629 / 1000000000000) (38068039636 / 1000000000000)))) (orderedInterval (-16317870632 / 1000000000000) (-16317870342 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate421_chunkChecks4_1 :
    compactCertificate421.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (523239906734883 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30654786063 / 1000000000000) (30654786189 / 1000000000000), orderedInterval (5776074772 / 1000000000000) (5776074897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (302092701004107 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40528787228 / 1000000000000) (40528787252 / 1000000000000), orderedInterval (6527255389 / 1000000000000) (6527255412 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (536068799152263 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30516326227 / 1000000000000) (-30516319333 / 1000000000000), orderedInterval (4359886154 / 1000000000000) (4359893048 / 1000000000000)))) (orderedInterval (-247337868044 / 1000000000000) (-247337837898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (500865009183747 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31663330437 / 1000000000000) (-31663326118 / 1000000000000), orderedInterval (3802296808 / 1000000000000) (3802301127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (357440904206451 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37591858916 / 1000000000000) (37591859027 / 1000000000000), orderedInterval (3377066309 / 1000000000000) (3377066421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (405299888971029 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35415944529 / 1000000000000) (-35415943602 / 1000000000000), orderedInterval (1551649500 / 1000000000000) (1551650427 / 1000000000000)))) (orderedInterval (32967913098 / 1000000000000) (32967915116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (337896792786501 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31779532829 / 1000000000000) (31779613012 / 1000000000000), orderedInterval (-22338128247 / 1000000000000) (-22338048064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (298542063808521 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4662127288 / 1000000000000) (-4662127287 / 1000000000000), orderedInterval (-41032872738 / 1000000000000) (-41032872737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (86529126327579 / 160000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32430380348 / 1000000000000) (32430380354 / 1000000000000), orderedInterval (11169848982 / 1000000000000) (11169848989 / 1000000000000)))) (orderedInterval (12046109271 / 1000000000000) (12046113465 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate421_chunkChecks4_2 :
    compactCertificate421.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (239344117200513 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46054087752 / 1000000000000) (-46054087690 / 1000000000000), orderedInterval (-2549652379 / 1000000000000) (-2549652317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (202894658814393 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3293095934 / 1000000000000) (3293095940 / 1000000000000), orderedInterval (-49999584931 / 1000000000000) (-49999584926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (126962056784979 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42426989024 / 1000000000000) (42427024948 / 1000000000000), orderedInterval (-47158707409 / 1000000000000) (-47158671485 / 1000000000000)))) (orderedInterval (8087779235 / 1000000000000) (8087779411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (68280616395693 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-83481364651 / 1000000000000) (-83481364650 / 1000000000000), orderedInterval (-21638200113 / 1000000000000) (-21638200112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (185395155986079 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2669128390 / 1000000000000) (2669128392 / 1000000000000), orderedInterval (52338914054 / 1000000000000) (52338914056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (253141235579583 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (4000625633 / 1000000000000) (4000625638 / 1000000000000), orderedInterval (-44681832550 / 1000000000000) (-44681832545 / 1000000000000)))) (orderedInterval (-406921476 / 1000000000000) (-406921441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (107037943215021 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (33468391944 / 1000000000000) (33468396323 / 1000000000000), orderedInterval (-60440665675 / 1000000000000) (-60440661296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (435103296600141 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31484891693 / 1000000000000) (-31484891691 / 1000000000000), orderedInterval (-13358298479 / 1000000000000) (-13358298477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (290628837674019 / 800000000000) 4 (IntervalRat.scale (585 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14497543474 / 1000000000000) (-14497543299 / 1000000000000), orderedInterval (39290999480 / 1000000000000) (39290999655 / 1000000000000)))) (orderedInterval (37068693102 / 1000000000000) (37068693600 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate421_chunkChecks4 :
    compactCertificate421.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate421.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate421_chunkChecks4_0
    compactCertificate421_chunkChecks4_1 compactCertificate421_chunkChecks4_2

theorem compactCertificate421_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate421.chunkCheck r b = true :=
  compactCertificate421.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate421_chunkChecks0
    · exact compactCertificate421_chunkChecks1
    · exact compactCertificate421_chunkChecks2
    · exact compactCertificate421_chunkChecks3
    · exact compactCertificate421_chunkChecks4)

theorem compactCertificate421_coefficient0 :
    compactCertificate421.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate421_coefficient1 :
    compactCertificate421.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate421_coefficient2 :
    compactCertificate421.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate421_coefficient3 :
    compactCertificate421.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate421_coefficient4 :
    compactCertificate421.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate421_coefficients : ∀ r : Fin 5,
    compactCertificate421.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate421_coefficient0
  · exact compactCertificate421_coefficient1
  · exact compactCertificate421_coefficient2
  · exact compactCertificate421_coefficient3
  · exact compactCertificate421_coefficient4

theorem compactCertificate421_lower : (1 : ℚ) ≤ compactCertificate421.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate421, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate421_proves {t : ℝ} (ht : t ∈ compactCertificate421.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate421.proves compactCertificate421_states compactCertificate421_chunks
    compactCertificate421_coefficients compactCertificate421_lower ht

end Erdos232
