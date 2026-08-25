/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate371 : CompactCertificate where
  left := 242
  right := 243
  center := 485 / 2
  grid := fun i =>
    match i.val with
    | 0 => 77
    | 1 => 57
    | 2 => 92
    | 3 => 17
    | 4 => 45
    | 5 => 121
    | 6 => 89
    | 7 => 153
    | 8 => 113
    | 9 => 173
    | 10 => 100
    | 11 => 177
    | 12 => 165
    | 13 => 118
    | 14 => 134
    | 15 => 112
    | 16 => 99
    | 17 => 143
    | 18 => 79
    | 19 => 67
    | 20 => 42
    | 21 => 23
    | 22 => 61
    | 23 => 84
    | 24 => 35
    | 25 => 144
    | _ => 96
  point := fun i =>
    match i.val with
    | 0 => 485 / 2
    | 1 => 142899521946397 / 800000000000
    | 2 => 46210769341501 / 160000000000
    | 3 => 41697724107479 / 800000000000
    | 4 => 112005952222763 / 800000000000
    | 5 => 304117948545471 / 800000000000
    | 6 => 224011904445623 / 800000000000
    | 7 => 383848216428179 / 800000000000
    | 8 => 282740858904761 / 800000000000
    | 9 => 433797187634903 / 800000000000
    | 10 => 250452923054687 / 800000000000
    | 11 => 444433106989483 / 800000000000
    | 12 => 415247058895927 / 800000000000
    | 13 => 296339894940391 / 800000000000
    | 14 => 336017856668289 / 800000000000
    | 15 => 280136657267441 / 800000000000
    | 16 => 247509232388261 / 800000000000
    | 17 => 71737822681839 / 160000000000
    | 18 => 198430592892733 / 800000000000
    | 19 => 168211811153813 / 800000000000
    | 20 => 105259141095239 / 800000000000
    | 21 => 56608716157113 / 800000000000
    | 22 => 153703676330339 / 800000000000
    | 23 => 209869229497603 / 800000000000
    | 24 => 88740858904761 / 800000000000
    | 25 => 360726664702681 / 800000000000
    | _ => 240948694481879 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-50328952890 / 1000000000000) (-50328952885 / 1000000000000), orderedInterval (-9499743758 / 1000000000000) (-9499743753 / 1000000000000))
    | 1 => (orderedInterval (-19814320485 / 1000000000000) (-19814320484 / 1000000000000), orderedInterval (-56259872512 / 1000000000000) (-56259872511 / 1000000000000))
    | 2 => (orderedInterval (25562131758 / 1000000000000) (25562131759 / 1000000000000), orderedInterval (39336056224 / 1000000000000) (39336056225 / 1000000000000))
    | 3 => (orderedInterval (53169497649 / 1000000000000) (53169503987 / 1000000000000), orderedInterval (-97398090022 / 1000000000000) (-97398083683 / 1000000000000))
    | 4 => (orderedInterval (36938514056 / 1000000000000) (36938523085 / 1000000000000), orderedInterval (-56546454790 / 1000000000000) (-56546445760 / 1000000000000))
    | 5 => (orderedInterval (-29350242883 / 1000000000000) (-29350242882 / 1000000000000), orderedInterval (-28478560265 / 1000000000000) (-28478560264 / 1000000000000))
    | 6 => (orderedInterval (-44407796599 / 1000000000000) (-44407796597 / 1000000000000), orderedInterval (-17283485608 / 1000000000000) (-17283485607 / 1000000000000))
    | 7 => (orderedInterval (2484756388 / 1000000000000) (2484756389 / 1000000000000), orderedInterval (-36343232422 / 1000000000000) (-36343232421 / 1000000000000))
    | 8 => (orderedInterval (30114112935 / 1000000000000) (30114137028 / 1000000000000), orderedInterval (-29949482350 / 1000000000000) (-29949458257 / 1000000000000))
    | 9 => (orderedInterval (15330477483 / 1000000000000) (15330477711 / 1000000000000), orderedInterval (-30657537826 / 1000000000000) (-30657537599 / 1000000000000))
    | 10 => (orderedInterval (-13675331848 / 1000000000000) (-13675331715 / 1000000000000), orderedInterval (42992605480 / 1000000000000) (42992605613 / 1000000000000))
    | 11 => (orderedInterval (-8854900618 / 1000000000000) (-8854900617 / 1000000000000), orderedInterval (-32665199173 / 1000000000000) (-32665199172 / 1000000000000))
    | 12 => (orderedInterval (-34880758261 / 1000000000000) (-34880758074 / 1000000000000), orderedInterval (-3100220689 / 1000000000000) (-3100220502 / 1000000000000))
    | 13 => (orderedInterval (19947762010 / 1000000000000) (19947762011 / 1000000000000), orderedInterval (36314622788 / 1000000000000) (36314622789 / 1000000000000))
    | 14 => (orderedInterval (-6432804176 / 1000000000000) (-6432804169 / 1000000000000), orderedInterval (38404283284 / 1000000000000) (38404283292 / 1000000000000))
    | 15 => (orderedInterval (-33466296506 / 1000000000000) (-33466228838 / 1000000000000), orderedInterval (26468104421 / 1000000000000) (26468172089 / 1000000000000))
    | 16 => (orderedInterval (33963439037 / 1000000000000) (33963488600 / 1000000000000), orderedInterval (-30124279903 / 1000000000000) (-30124230341 / 1000000000000))
    | 17 => (orderedInterval (3808278335 / 1000000000000) (3808278338 / 1000000000000), orderedInterval (-37492628705 / 1000000000000) (-37492628703 / 1000000000000))
    | 18 => (orderedInterval (-30145786750 / 1000000000000) (-30145786749 / 1000000000000), orderedInterval (-40655966792 / 1000000000000) (-40655966791 / 1000000000000))
    | 19 => (orderedInterval (-29361466348 / 1000000000000) (-29361466347 / 1000000000000), orderedInterval (-46466332055 / 1000000000000) (-46466332054 / 1000000000000))
    | 20 => (orderedInterval (27821462737 / 1000000000000) (27821462738 / 1000000000000), orderedInterval (63647588574 / 1000000000000) (63647588575 / 1000000000000))
    | 21 => (orderedInterval (61977707484 / 1000000000000) (61977751124 / 1000000000000), orderedInterval (-72240217239 / 1000000000000) (-72240173599 / 1000000000000))
    | 22 => (orderedInterval (-55099535324 / 1000000000000) (-55099535323 / 1000000000000), orderedInterval (-16515640575 / 1000000000000) (-16515640573 / 1000000000000))
    | 23 => (orderedInterval (-34374999307 / 1000000000000) (-34374967665 / 1000000000000), orderedInterval (35351332284 / 1000000000000) (35351363926 / 1000000000000))
    | 24 => (orderedInterval (-74480593461 / 1000000000000) (-74480593011 / 1000000000000), orderedInterval (14182099700 / 1000000000000) (14182100150 / 1000000000000))
    | 25 => (orderedInterval (-24087992747 / 1000000000000) (-24087986802 / 1000000000000), orderedInterval (28864697064 / 1000000000000) (28864703009 / 1000000000000))
    | _ => (orderedInterval (16965813445 / 1000000000000) (16965813446 / 1000000000000), orderedInterval (42702081110 / 1000000000000) (42702081111 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-18633251063 / 1000000000000) (-18633251044 / 1000000000000)
      | 1 => orderedInterval (2858336437 / 1000000000000) (2858336865 / 1000000000000)
      | 2 => orderedInterval (651158859 / 1000000000000) (651159455 / 1000000000000)
      | 3 => orderedInterval (-4996046689 / 1000000000000) (-4996046542 / 1000000000000)
      | 4 => orderedInterval (2548576551 / 1000000000000) (2548576584 / 1000000000000)
      | 5 => orderedInterval (-2232568384 / 1000000000000) (-2232564742 / 1000000000000)
      | 6 => orderedInterval (7387676391 / 1000000000000) (7387676453 / 1000000000000)
      | 7 => orderedInterval (2740067792 / 1000000000000) (2740071052 / 1000000000000)
      | _ => orderedInterval (-1671425205 / 1000000000000) (-1671424651 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1402348274 / 1000000000000) (-1402348253 / 1000000000000)
      | 1 => orderedInterval (2208811870 / 1000000000000) (2208812109 / 1000000000000)
      | 2 => orderedInterval (1163036808 / 1000000000000) (1163037681 / 1000000000000)
      | 3 => orderedInterval (5655380012 / 1000000000000) (5655380315 / 1000000000000)
      | 4 => orderedInterval (5028721796 / 1000000000000) (5028721851 / 1000000000000)
      | 5 => orderedInterval (865870650 / 1000000000000) (865875431 / 1000000000000)
      | 6 => orderedInterval (10053679397 / 1000000000000) (10053679454 / 1000000000000)
      | 7 => orderedInterval (-2244812861 / 1000000000000) (-2244809976 / 1000000000000)
      | _ => orderedInterval (-14280833153 / 1000000000000) (-14280832157 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17926853717 / 1000000000000) (17926853741 / 1000000000000)
      | 1 => orderedInterval (-5559439901 / 1000000000000) (-5559439740 / 1000000000000)
      | 2 => orderedInterval (-1250676210 / 1000000000000) (-1250674927 / 1000000000000)
      | 3 => orderedInterval (21891892365 / 1000000000000) (21891893013 / 1000000000000)
      | 4 => orderedInterval (-7404813840 / 1000000000000) (-7404813746 / 1000000000000)
      | 5 => orderedInterval (3632580973 / 1000000000000) (3632587290 / 1000000000000)
      | 6 => orderedInterval (-6600259683 / 1000000000000) (-6600259628 / 1000000000000)
      | 7 => orderedInterval (-3761058329 / 1000000000000) (-3761055384 / 1000000000000)
      | _ => orderedInterval (-1716130069 / 1000000000000) (-1716128251 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (1296661 / 1000000000000) (1296689 / 1000000000000)
      | 1 => orderedInterval (-7389310170 / 1000000000000) (-7389310036 / 1000000000000)
      | 2 => orderedInterval (-6437043825 / 1000000000000) (-6437041940 / 1000000000000)
      | 3 => orderedInterval (-12019121609 / 1000000000000) (-12019120198 / 1000000000000)
      | 4 => orderedInterval (-11747977954 / 1000000000000) (-11747977788 / 1000000000000)
      | 5 => orderedInterval (1552133645 / 1000000000000) (1552141992 / 1000000000000)
      | 6 => orderedInterval (-8974213010 / 1000000000000) (-8974212957 / 1000000000000)
      | 7 => orderedInterval (3225999466 / 1000000000000) (3226002596 / 1000000000000)
      | _ => orderedInterval (30454110456 / 1000000000000) (30454113790 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16984538735 / 1000000000000) (-16984538703 / 1000000000000)
      | 1 => orderedInterval (12809725575 / 1000000000000) (12809725719 / 1000000000000)
      | 2 => orderedInterval (2162142663 / 1000000000000) (2162145447 / 1000000000000)
      | 3 => orderedInterval (-105487119016 / 1000000000000) (-105487115890 / 1000000000000)
      | 4 => orderedInterval (23877423329 / 1000000000000) (23877423630 / 1000000000000)
      | 5 => orderedInterval (-5703079661 / 1000000000000) (-5703068557 / 1000000000000)
      | 6 => orderedInterval (6367438228 / 1000000000000) (6367438280 / 1000000000000)
      | 7 => orderedInterval (4065693667 / 1000000000000) (4065697048 / 1000000000000)
      | _ => orderedInterval (15593609819 / 1000000000000) (15593615976 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-11347475311 / 1000000000000) (-11347466570 / 1000000000000)
    | 1 => orderedInterval (7047506245 / 1000000000000) (7047516455 / 1000000000000)
    | 2 => orderedInterval (17158949023 / 1000000000000) (17158962368 / 1000000000000)
    | 3 => orderedInterval (-11334126340 / 1000000000000) (-11334107852 / 1000000000000)
    | _ => orderedInterval (-63298704131 / 1000000000000) (-63298677050 / 1000000000000)

theorem compactCertificate371_stateChecks0 :
    compactCertificate371.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (485 / 2)) (orderedInterval (-50328952890 / 1000000000000) (-50328952885 / 1000000000000), orderedInterval (-9499743758 / 1000000000000) (-9499743753 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (142899521946397 / 800000000000)) (orderedInterval (-19814320485 / 1000000000000) (-19814320484 / 1000000000000), orderedInterval (-56259872512 / 1000000000000) (-56259872511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (46210769341501 / 160000000000)) (orderedInterval (25562131758 / 1000000000000) (25562131759 / 1000000000000), orderedInterval (39336056224 / 1000000000000) (39336056225 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_stateChecks1 :
    compactCertificate371.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (41697724107479 / 800000000000)) (orderedInterval (53169497649 / 1000000000000) (53169503987 / 1000000000000), orderedInterval (-97398090022 / 1000000000000) (-97398083683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (112005952222763 / 800000000000)) (orderedInterval (36938514056 / 1000000000000) (36938523085 / 1000000000000), orderedInterval (-56546454790 / 1000000000000) (-56546445760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (304117948545471 / 800000000000)) (orderedInterval (-29350242883 / 1000000000000) (-29350242882 / 1000000000000), orderedInterval (-28478560265 / 1000000000000) (-28478560264 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_stateChecks2 :
    compactCertificate371.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (224011904445623 / 800000000000)) (orderedInterval (-44407796599 / 1000000000000) (-44407796597 / 1000000000000), orderedInterval (-17283485608 / 1000000000000) (-17283485607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (383848216428179 / 800000000000)) (orderedInterval (2484756388 / 1000000000000) (2484756389 / 1000000000000), orderedInterval (-36343232422 / 1000000000000) (-36343232421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (282740858904761 / 800000000000)) (orderedInterval (30114112935 / 1000000000000) (30114137028 / 1000000000000), orderedInterval (-29949482350 / 1000000000000) (-29949458257 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_stateChecks3 :
    compactCertificate371.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (433797187634903 / 800000000000)) (orderedInterval (15330477483 / 1000000000000) (15330477711 / 1000000000000), orderedInterval (-30657537826 / 1000000000000) (-30657537599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (250452923054687 / 800000000000)) (orderedInterval (-13675331848 / 1000000000000) (-13675331715 / 1000000000000), orderedInterval (42992605480 / 1000000000000) (42992605613 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (444433106989483 / 800000000000)) (orderedInterval (-8854900618 / 1000000000000) (-8854900617 / 1000000000000), orderedInterval (-32665199173 / 1000000000000) (-32665199172 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_stateChecks4 :
    compactCertificate371.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (415247058895927 / 800000000000)) (orderedInterval (-34880758261 / 1000000000000) (-34880758074 / 1000000000000), orderedInterval (-3100220689 / 1000000000000) (-3100220502 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (296339894940391 / 800000000000)) (orderedInterval (19947762010 / 1000000000000) (19947762011 / 1000000000000), orderedInterval (36314622788 / 1000000000000) (36314622789 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (336017856668289 / 800000000000)) (orderedInterval (-6432804176 / 1000000000000) (-6432804169 / 1000000000000), orderedInterval (38404283284 / 1000000000000) (38404283292 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_stateChecks5 :
    compactCertificate371.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (280136657267441 / 800000000000)) (orderedInterval (-33466296506 / 1000000000000) (-33466228838 / 1000000000000), orderedInterval (26468104421 / 1000000000000) (26468172089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (247509232388261 / 800000000000)) (orderedInterval (33963439037 / 1000000000000) (33963488600 / 1000000000000), orderedInterval (-30124279903 / 1000000000000) (-30124230341 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (71737822681839 / 160000000000)) (orderedInterval (3808278335 / 1000000000000) (3808278338 / 1000000000000), orderedInterval (-37492628705 / 1000000000000) (-37492628703 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_stateChecks6 :
    compactCertificate371.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (198430592892733 / 800000000000)) (orderedInterval (-30145786750 / 1000000000000) (-30145786749 / 1000000000000), orderedInterval (-40655966792 / 1000000000000) (-40655966791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (168211811153813 / 800000000000)) (orderedInterval (-29361466348 / 1000000000000) (-29361466347 / 1000000000000), orderedInterval (-46466332055 / 1000000000000) (-46466332054 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (105259141095239 / 800000000000)) (orderedInterval (27821462737 / 1000000000000) (27821462738 / 1000000000000), orderedInterval (63647588574 / 1000000000000) (63647588575 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_stateChecks7 :
    compactCertificate371.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (56608716157113 / 800000000000)) (orderedInterval (61977707484 / 1000000000000) (61977751124 / 1000000000000), orderedInterval (-72240217239 / 1000000000000) (-72240173599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (153703676330339 / 800000000000)) (orderedInterval (-55099535324 / 1000000000000) (-55099535323 / 1000000000000), orderedInterval (-16515640575 / 1000000000000) (-16515640573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (209869229497603 / 800000000000)) (orderedInterval (-34374999307 / 1000000000000) (-34374967665 / 1000000000000), orderedInterval (35351332284 / 1000000000000) (35351363926 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_stateChecks8 :
    compactCertificate371.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (88740858904761 / 800000000000)) (orderedInterval (-74480593461 / 1000000000000) (-74480593011 / 1000000000000), orderedInterval (14182099700 / 1000000000000) (14182100150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (360726664702681 / 800000000000)) (orderedInterval (-24087992747 / 1000000000000) (-24087986802 / 1000000000000), orderedInterval (28864697064 / 1000000000000) (28864703009 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (240948694481879 / 800000000000)) (orderedInterval (16965813445 / 1000000000000) (16965813446 / 1000000000000), orderedInterval (42702081110 / 1000000000000) (42702081111 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_states : ∀ j,
    BesselStateValid (compactCertificate371.point j) (compactCertificate371.state j) :=
  compactCertificate371.statesValid_of_checks3 compactCertificate371_stateChecks0
    compactCertificate371_stateChecks1 compactCertificate371_stateChecks2
    compactCertificate371_stateChecks3 compactCertificate371_stateChecks4
    compactCertificate371_stateChecks5 compactCertificate371_stateChecks6
    compactCertificate371_stateChecks7 compactCertificate371_stateChecks8

theorem compactCertificate371_chunkChecks0_0 :
    compactCertificate371.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (485 / 2) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50328952890 / 1000000000000) (-50328952885 / 1000000000000), orderedInterval (-9499743758 / 1000000000000) (-9499743753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (142899521946397 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19814320485 / 1000000000000) (-19814320484 / 1000000000000), orderedInterval (-56259872512 / 1000000000000) (-56259872511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (46210769341501 / 160000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25562131758 / 1000000000000) (25562131759 / 1000000000000), orderedInterval (39336056224 / 1000000000000) (39336056225 / 1000000000000)))) (orderedInterval (-18633251063 / 1000000000000) (-18633251044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (41697724107479 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53169497649 / 1000000000000) (53169503987 / 1000000000000), orderedInterval (-97398090022 / 1000000000000) (-97398083683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (112005952222763 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36938514056 / 1000000000000) (36938523085 / 1000000000000), orderedInterval (-56546454790 / 1000000000000) (-56546445760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (304117948545471 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29350242883 / 1000000000000) (-29350242882 / 1000000000000), orderedInterval (-28478560265 / 1000000000000) (-28478560264 / 1000000000000)))) (orderedInterval (2858336437 / 1000000000000) (2858336865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (224011904445623 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44407796599 / 1000000000000) (-44407796597 / 1000000000000), orderedInterval (-17283485608 / 1000000000000) (-17283485607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (383848216428179 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2484756388 / 1000000000000) (2484756389 / 1000000000000), orderedInterval (-36343232422 / 1000000000000) (-36343232421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (282740858904761 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30114112935 / 1000000000000) (30114137028 / 1000000000000), orderedInterval (-29949482350 / 1000000000000) (-29949458257 / 1000000000000)))) (orderedInterval (651158859 / 1000000000000) (651159455 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks0_1 :
    compactCertificate371.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (433797187634903 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15330477483 / 1000000000000) (15330477711 / 1000000000000), orderedInterval (-30657537826 / 1000000000000) (-30657537599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (250452923054687 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13675331848 / 1000000000000) (-13675331715 / 1000000000000), orderedInterval (42992605480 / 1000000000000) (42992605613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (444433106989483 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8854900618 / 1000000000000) (-8854900617 / 1000000000000), orderedInterval (-32665199173 / 1000000000000) (-32665199172 / 1000000000000)))) (orderedInterval (-4996046689 / 1000000000000) (-4996046542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (415247058895927 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34880758261 / 1000000000000) (-34880758074 / 1000000000000), orderedInterval (-3100220689 / 1000000000000) (-3100220502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (296339894940391 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19947762010 / 1000000000000) (19947762011 / 1000000000000), orderedInterval (36314622788 / 1000000000000) (36314622789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (336017856668289 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6432804176 / 1000000000000) (-6432804169 / 1000000000000), orderedInterval (38404283284 / 1000000000000) (38404283292 / 1000000000000)))) (orderedInterval (2548576551 / 1000000000000) (2548576584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (280136657267441 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33466296506 / 1000000000000) (-33466228838 / 1000000000000), orderedInterval (26468104421 / 1000000000000) (26468172089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (247509232388261 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33963439037 / 1000000000000) (33963488600 / 1000000000000), orderedInterval (-30124279903 / 1000000000000) (-30124230341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (71737822681839 / 160000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3808278335 / 1000000000000) (3808278338 / 1000000000000), orderedInterval (-37492628705 / 1000000000000) (-37492628703 / 1000000000000)))) (orderedInterval (-2232568384 / 1000000000000) (-2232564742 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks0_2 :
    compactCertificate371.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (198430592892733 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30145786750 / 1000000000000) (-30145786749 / 1000000000000), orderedInterval (-40655966792 / 1000000000000) (-40655966791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (168211811153813 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29361466348 / 1000000000000) (-29361466347 / 1000000000000), orderedInterval (-46466332055 / 1000000000000) (-46466332054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (105259141095239 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27821462737 / 1000000000000) (27821462738 / 1000000000000), orderedInterval (63647588574 / 1000000000000) (63647588575 / 1000000000000)))) (orderedInterval (7387676391 / 1000000000000) (7387676453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (56608716157113 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61977707484 / 1000000000000) (61977751124 / 1000000000000), orderedInterval (-72240217239 / 1000000000000) (-72240173599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (153703676330339 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55099535324 / 1000000000000) (-55099535323 / 1000000000000), orderedInterval (-16515640575 / 1000000000000) (-16515640573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (209869229497603 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34374999307 / 1000000000000) (-34374967665 / 1000000000000), orderedInterval (35351332284 / 1000000000000) (35351363926 / 1000000000000)))) (orderedInterval (2740067792 / 1000000000000) (2740071052 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (88740858904761 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74480593461 / 1000000000000) (-74480593011 / 1000000000000), orderedInterval (14182099700 / 1000000000000) (14182100150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (360726664702681 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24087992747 / 1000000000000) (-24087986802 / 1000000000000), orderedInterval (28864697064 / 1000000000000) (28864703009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (240948694481879 / 800000000000) 0 (IntervalRat.scale (485 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16965813445 / 1000000000000) (16965813446 / 1000000000000), orderedInterval (42702081110 / 1000000000000) (42702081111 / 1000000000000)))) (orderedInterval (-1671425205 / 1000000000000) (-1671424651 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks0 :
    compactCertificate371.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate371.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate371_chunkChecks0_0
    compactCertificate371_chunkChecks0_1 compactCertificate371_chunkChecks0_2

theorem compactCertificate371_chunkChecks1_0 :
    compactCertificate371.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (485 / 2) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50328952890 / 1000000000000) (-50328952885 / 1000000000000), orderedInterval (-9499743758 / 1000000000000) (-9499743753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (142899521946397 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19814320485 / 1000000000000) (-19814320484 / 1000000000000), orderedInterval (-56259872512 / 1000000000000) (-56259872511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (46210769341501 / 160000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25562131758 / 1000000000000) (25562131759 / 1000000000000), orderedInterval (39336056224 / 1000000000000) (39336056225 / 1000000000000)))) (orderedInterval (-1402348274 / 1000000000000) (-1402348253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (41697724107479 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53169497649 / 1000000000000) (53169503987 / 1000000000000), orderedInterval (-97398090022 / 1000000000000) (-97398083683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (112005952222763 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36938514056 / 1000000000000) (36938523085 / 1000000000000), orderedInterval (-56546454790 / 1000000000000) (-56546445760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (304117948545471 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29350242883 / 1000000000000) (-29350242882 / 1000000000000), orderedInterval (-28478560265 / 1000000000000) (-28478560264 / 1000000000000)))) (orderedInterval (2208811870 / 1000000000000) (2208812109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (224011904445623 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44407796599 / 1000000000000) (-44407796597 / 1000000000000), orderedInterval (-17283485608 / 1000000000000) (-17283485607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (383848216428179 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2484756388 / 1000000000000) (2484756389 / 1000000000000), orderedInterval (-36343232422 / 1000000000000) (-36343232421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (282740858904761 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30114112935 / 1000000000000) (30114137028 / 1000000000000), orderedInterval (-29949482350 / 1000000000000) (-29949458257 / 1000000000000)))) (orderedInterval (1163036808 / 1000000000000) (1163037681 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks1_1 :
    compactCertificate371.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (433797187634903 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15330477483 / 1000000000000) (15330477711 / 1000000000000), orderedInterval (-30657537826 / 1000000000000) (-30657537599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (250452923054687 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13675331848 / 1000000000000) (-13675331715 / 1000000000000), orderedInterval (42992605480 / 1000000000000) (42992605613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (444433106989483 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8854900618 / 1000000000000) (-8854900617 / 1000000000000), orderedInterval (-32665199173 / 1000000000000) (-32665199172 / 1000000000000)))) (orderedInterval (5655380012 / 1000000000000) (5655380315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (415247058895927 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34880758261 / 1000000000000) (-34880758074 / 1000000000000), orderedInterval (-3100220689 / 1000000000000) (-3100220502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (296339894940391 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19947762010 / 1000000000000) (19947762011 / 1000000000000), orderedInterval (36314622788 / 1000000000000) (36314622789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (336017856668289 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6432804176 / 1000000000000) (-6432804169 / 1000000000000), orderedInterval (38404283284 / 1000000000000) (38404283292 / 1000000000000)))) (orderedInterval (5028721796 / 1000000000000) (5028721851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (280136657267441 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33466296506 / 1000000000000) (-33466228838 / 1000000000000), orderedInterval (26468104421 / 1000000000000) (26468172089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (247509232388261 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33963439037 / 1000000000000) (33963488600 / 1000000000000), orderedInterval (-30124279903 / 1000000000000) (-30124230341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (71737822681839 / 160000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3808278335 / 1000000000000) (3808278338 / 1000000000000), orderedInterval (-37492628705 / 1000000000000) (-37492628703 / 1000000000000)))) (orderedInterval (865870650 / 1000000000000) (865875431 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks1_2 :
    compactCertificate371.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (198430592892733 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30145786750 / 1000000000000) (-30145786749 / 1000000000000), orderedInterval (-40655966792 / 1000000000000) (-40655966791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (168211811153813 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29361466348 / 1000000000000) (-29361466347 / 1000000000000), orderedInterval (-46466332055 / 1000000000000) (-46466332054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (105259141095239 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27821462737 / 1000000000000) (27821462738 / 1000000000000), orderedInterval (63647588574 / 1000000000000) (63647588575 / 1000000000000)))) (orderedInterval (10053679397 / 1000000000000) (10053679454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (56608716157113 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61977707484 / 1000000000000) (61977751124 / 1000000000000), orderedInterval (-72240217239 / 1000000000000) (-72240173599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (153703676330339 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55099535324 / 1000000000000) (-55099535323 / 1000000000000), orderedInterval (-16515640575 / 1000000000000) (-16515640573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (209869229497603 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34374999307 / 1000000000000) (-34374967665 / 1000000000000), orderedInterval (35351332284 / 1000000000000) (35351363926 / 1000000000000)))) (orderedInterval (-2244812861 / 1000000000000) (-2244809976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (88740858904761 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74480593461 / 1000000000000) (-74480593011 / 1000000000000), orderedInterval (14182099700 / 1000000000000) (14182100150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (360726664702681 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24087992747 / 1000000000000) (-24087986802 / 1000000000000), orderedInterval (28864697064 / 1000000000000) (28864703009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (240948694481879 / 800000000000) 1 (IntervalRat.scale (485 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16965813445 / 1000000000000) (16965813446 / 1000000000000), orderedInterval (42702081110 / 1000000000000) (42702081111 / 1000000000000)))) (orderedInterval (-14280833153 / 1000000000000) (-14280832157 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks1 :
    compactCertificate371.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate371.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate371_chunkChecks1_0
    compactCertificate371_chunkChecks1_1 compactCertificate371_chunkChecks1_2

theorem compactCertificate371_chunkChecks2_0 :
    compactCertificate371.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (485 / 2) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50328952890 / 1000000000000) (-50328952885 / 1000000000000), orderedInterval (-9499743758 / 1000000000000) (-9499743753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (142899521946397 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19814320485 / 1000000000000) (-19814320484 / 1000000000000), orderedInterval (-56259872512 / 1000000000000) (-56259872511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (46210769341501 / 160000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25562131758 / 1000000000000) (25562131759 / 1000000000000), orderedInterval (39336056224 / 1000000000000) (39336056225 / 1000000000000)))) (orderedInterval (17926853717 / 1000000000000) (17926853741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (41697724107479 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53169497649 / 1000000000000) (53169503987 / 1000000000000), orderedInterval (-97398090022 / 1000000000000) (-97398083683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (112005952222763 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36938514056 / 1000000000000) (36938523085 / 1000000000000), orderedInterval (-56546454790 / 1000000000000) (-56546445760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (304117948545471 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29350242883 / 1000000000000) (-29350242882 / 1000000000000), orderedInterval (-28478560265 / 1000000000000) (-28478560264 / 1000000000000)))) (orderedInterval (-5559439901 / 1000000000000) (-5559439740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (224011904445623 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44407796599 / 1000000000000) (-44407796597 / 1000000000000), orderedInterval (-17283485608 / 1000000000000) (-17283485607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (383848216428179 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2484756388 / 1000000000000) (2484756389 / 1000000000000), orderedInterval (-36343232422 / 1000000000000) (-36343232421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (282740858904761 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30114112935 / 1000000000000) (30114137028 / 1000000000000), orderedInterval (-29949482350 / 1000000000000) (-29949458257 / 1000000000000)))) (orderedInterval (-1250676210 / 1000000000000) (-1250674927 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks2_1 :
    compactCertificate371.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (433797187634903 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15330477483 / 1000000000000) (15330477711 / 1000000000000), orderedInterval (-30657537826 / 1000000000000) (-30657537599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (250452923054687 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13675331848 / 1000000000000) (-13675331715 / 1000000000000), orderedInterval (42992605480 / 1000000000000) (42992605613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (444433106989483 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8854900618 / 1000000000000) (-8854900617 / 1000000000000), orderedInterval (-32665199173 / 1000000000000) (-32665199172 / 1000000000000)))) (orderedInterval (21891892365 / 1000000000000) (21891893013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (415247058895927 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34880758261 / 1000000000000) (-34880758074 / 1000000000000), orderedInterval (-3100220689 / 1000000000000) (-3100220502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (296339894940391 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19947762010 / 1000000000000) (19947762011 / 1000000000000), orderedInterval (36314622788 / 1000000000000) (36314622789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (336017856668289 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6432804176 / 1000000000000) (-6432804169 / 1000000000000), orderedInterval (38404283284 / 1000000000000) (38404283292 / 1000000000000)))) (orderedInterval (-7404813840 / 1000000000000) (-7404813746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (280136657267441 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33466296506 / 1000000000000) (-33466228838 / 1000000000000), orderedInterval (26468104421 / 1000000000000) (26468172089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (247509232388261 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33963439037 / 1000000000000) (33963488600 / 1000000000000), orderedInterval (-30124279903 / 1000000000000) (-30124230341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (71737822681839 / 160000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3808278335 / 1000000000000) (3808278338 / 1000000000000), orderedInterval (-37492628705 / 1000000000000) (-37492628703 / 1000000000000)))) (orderedInterval (3632580973 / 1000000000000) (3632587290 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks2_2 :
    compactCertificate371.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (198430592892733 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30145786750 / 1000000000000) (-30145786749 / 1000000000000), orderedInterval (-40655966792 / 1000000000000) (-40655966791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (168211811153813 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29361466348 / 1000000000000) (-29361466347 / 1000000000000), orderedInterval (-46466332055 / 1000000000000) (-46466332054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (105259141095239 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27821462737 / 1000000000000) (27821462738 / 1000000000000), orderedInterval (63647588574 / 1000000000000) (63647588575 / 1000000000000)))) (orderedInterval (-6600259683 / 1000000000000) (-6600259628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (56608716157113 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61977707484 / 1000000000000) (61977751124 / 1000000000000), orderedInterval (-72240217239 / 1000000000000) (-72240173599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (153703676330339 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55099535324 / 1000000000000) (-55099535323 / 1000000000000), orderedInterval (-16515640575 / 1000000000000) (-16515640573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (209869229497603 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34374999307 / 1000000000000) (-34374967665 / 1000000000000), orderedInterval (35351332284 / 1000000000000) (35351363926 / 1000000000000)))) (orderedInterval (-3761058329 / 1000000000000) (-3761055384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (88740858904761 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74480593461 / 1000000000000) (-74480593011 / 1000000000000), orderedInterval (14182099700 / 1000000000000) (14182100150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (360726664702681 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24087992747 / 1000000000000) (-24087986802 / 1000000000000), orderedInterval (28864697064 / 1000000000000) (28864703009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (240948694481879 / 800000000000) 2 (IntervalRat.scale (485 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16965813445 / 1000000000000) (16965813446 / 1000000000000), orderedInterval (42702081110 / 1000000000000) (42702081111 / 1000000000000)))) (orderedInterval (-1716130069 / 1000000000000) (-1716128251 / 1000000000000))) = true
  rfl'

theorem compactCertificate371_chunkChecks2 :
    compactCertificate371.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate371.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate371_chunkChecks2_0
    compactCertificate371_chunkChecks2_1 compactCertificate371_chunkChecks2_2

theorem compactCertificate371_chunkChecks3_0 :
    compactCertificate371.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (485 / 2) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50328952890 / 1000000000000) (-50328952885 / 1000000000000), orderedInterval (-9499743758 / 1000000000000) (-9499743753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (142899521946397 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19814320485 / 1000000000000) (-19814320484 / 1000000000000), orderedInterval (-56259872512 / 1000000000000) (-56259872511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (46210769341501 / 160000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25562131758 / 1000000000000) (25562131759 / 1000000000000), orderedInterval (39336056224 / 1000000000000) (39336056225 / 1000000000000)))) (orderedInterval (1296661 / 1000000000000) (1296689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (41697724107479 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53169497649 / 1000000000000) (53169503987 / 1000000000000), orderedInterval (-97398090022 / 1000000000000) (-97398083683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (112005952222763 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36938514056 / 1000000000000) (36938523085 / 1000000000000), orderedInterval (-56546454790 / 1000000000000) (-56546445760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (304117948545471 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29350242883 / 1000000000000) (-29350242882 / 1000000000000), orderedInterval (-28478560265 / 1000000000000) (-28478560264 / 1000000000000)))) (orderedInterval (-7389310170 / 1000000000000) (-7389310036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (224011904445623 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44407796599 / 1000000000000) (-44407796597 / 1000000000000), orderedInterval (-17283485608 / 1000000000000) (-17283485607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (383848216428179 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2484756388 / 1000000000000) (2484756389 / 1000000000000), orderedInterval (-36343232422 / 1000000000000) (-36343232421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (282740858904761 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30114112935 / 1000000000000) (30114137028 / 1000000000000), orderedInterval (-29949482350 / 1000000000000) (-29949458257 / 1000000000000)))) (orderedInterval (-6437043825 / 1000000000000) (-6437041940 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate371_chunkChecks3_1 :
    compactCertificate371.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (433797187634903 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15330477483 / 1000000000000) (15330477711 / 1000000000000), orderedInterval (-30657537826 / 1000000000000) (-30657537599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (250452923054687 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13675331848 / 1000000000000) (-13675331715 / 1000000000000), orderedInterval (42992605480 / 1000000000000) (42992605613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (444433106989483 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8854900618 / 1000000000000) (-8854900617 / 1000000000000), orderedInterval (-32665199173 / 1000000000000) (-32665199172 / 1000000000000)))) (orderedInterval (-12019121609 / 1000000000000) (-12019120198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (415247058895927 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34880758261 / 1000000000000) (-34880758074 / 1000000000000), orderedInterval (-3100220689 / 1000000000000) (-3100220502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (296339894940391 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19947762010 / 1000000000000) (19947762011 / 1000000000000), orderedInterval (36314622788 / 1000000000000) (36314622789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (336017856668289 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6432804176 / 1000000000000) (-6432804169 / 1000000000000), orderedInterval (38404283284 / 1000000000000) (38404283292 / 1000000000000)))) (orderedInterval (-11747977954 / 1000000000000) (-11747977788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (280136657267441 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33466296506 / 1000000000000) (-33466228838 / 1000000000000), orderedInterval (26468104421 / 1000000000000) (26468172089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (247509232388261 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33963439037 / 1000000000000) (33963488600 / 1000000000000), orderedInterval (-30124279903 / 1000000000000) (-30124230341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (71737822681839 / 160000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3808278335 / 1000000000000) (3808278338 / 1000000000000), orderedInterval (-37492628705 / 1000000000000) (-37492628703 / 1000000000000)))) (orderedInterval (1552133645 / 1000000000000) (1552141992 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate371_chunkChecks3_2 :
    compactCertificate371.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (198430592892733 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30145786750 / 1000000000000) (-30145786749 / 1000000000000), orderedInterval (-40655966792 / 1000000000000) (-40655966791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (168211811153813 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29361466348 / 1000000000000) (-29361466347 / 1000000000000), orderedInterval (-46466332055 / 1000000000000) (-46466332054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (105259141095239 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27821462737 / 1000000000000) (27821462738 / 1000000000000), orderedInterval (63647588574 / 1000000000000) (63647588575 / 1000000000000)))) (orderedInterval (-8974213010 / 1000000000000) (-8974212957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (56608716157113 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61977707484 / 1000000000000) (61977751124 / 1000000000000), orderedInterval (-72240217239 / 1000000000000) (-72240173599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (153703676330339 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55099535324 / 1000000000000) (-55099535323 / 1000000000000), orderedInterval (-16515640575 / 1000000000000) (-16515640573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (209869229497603 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34374999307 / 1000000000000) (-34374967665 / 1000000000000), orderedInterval (35351332284 / 1000000000000) (35351363926 / 1000000000000)))) (orderedInterval (3225999466 / 1000000000000) (3226002596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (88740858904761 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74480593461 / 1000000000000) (-74480593011 / 1000000000000), orderedInterval (14182099700 / 1000000000000) (14182100150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (360726664702681 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24087992747 / 1000000000000) (-24087986802 / 1000000000000), orderedInterval (28864697064 / 1000000000000) (28864703009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (240948694481879 / 800000000000) 3 (IntervalRat.scale (485 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16965813445 / 1000000000000) (16965813446 / 1000000000000), orderedInterval (42702081110 / 1000000000000) (42702081111 / 1000000000000)))) (orderedInterval (30454110456 / 1000000000000) (30454113790 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate371_chunkChecks3 :
    compactCertificate371.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate371.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate371_chunkChecks3_0
    compactCertificate371_chunkChecks3_1 compactCertificate371_chunkChecks3_2

theorem compactCertificate371_chunkChecks4_0 :
    compactCertificate371.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (485 / 2) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50328952890 / 1000000000000) (-50328952885 / 1000000000000), orderedInterval (-9499743758 / 1000000000000) (-9499743753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (142899521946397 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19814320485 / 1000000000000) (-19814320484 / 1000000000000), orderedInterval (-56259872512 / 1000000000000) (-56259872511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (46210769341501 / 160000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25562131758 / 1000000000000) (25562131759 / 1000000000000), orderedInterval (39336056224 / 1000000000000) (39336056225 / 1000000000000)))) (orderedInterval (-16984538735 / 1000000000000) (-16984538703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (41697724107479 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53169497649 / 1000000000000) (53169503987 / 1000000000000), orderedInterval (-97398090022 / 1000000000000) (-97398083683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (112005952222763 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36938514056 / 1000000000000) (36938523085 / 1000000000000), orderedInterval (-56546454790 / 1000000000000) (-56546445760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (304117948545471 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29350242883 / 1000000000000) (-29350242882 / 1000000000000), orderedInterval (-28478560265 / 1000000000000) (-28478560264 / 1000000000000)))) (orderedInterval (12809725575 / 1000000000000) (12809725719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (224011904445623 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44407796599 / 1000000000000) (-44407796597 / 1000000000000), orderedInterval (-17283485608 / 1000000000000) (-17283485607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (383848216428179 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2484756388 / 1000000000000) (2484756389 / 1000000000000), orderedInterval (-36343232422 / 1000000000000) (-36343232421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (282740858904761 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30114112935 / 1000000000000) (30114137028 / 1000000000000), orderedInterval (-29949482350 / 1000000000000) (-29949458257 / 1000000000000)))) (orderedInterval (2162142663 / 1000000000000) (2162145447 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate371_chunkChecks4_1 :
    compactCertificate371.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (433797187634903 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15330477483 / 1000000000000) (15330477711 / 1000000000000), orderedInterval (-30657537826 / 1000000000000) (-30657537599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (250452923054687 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13675331848 / 1000000000000) (-13675331715 / 1000000000000), orderedInterval (42992605480 / 1000000000000) (42992605613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (444433106989483 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8854900618 / 1000000000000) (-8854900617 / 1000000000000), orderedInterval (-32665199173 / 1000000000000) (-32665199172 / 1000000000000)))) (orderedInterval (-105487119016 / 1000000000000) (-105487115890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (415247058895927 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34880758261 / 1000000000000) (-34880758074 / 1000000000000), orderedInterval (-3100220689 / 1000000000000) (-3100220502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (296339894940391 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19947762010 / 1000000000000) (19947762011 / 1000000000000), orderedInterval (36314622788 / 1000000000000) (36314622789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (336017856668289 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6432804176 / 1000000000000) (-6432804169 / 1000000000000), orderedInterval (38404283284 / 1000000000000) (38404283292 / 1000000000000)))) (orderedInterval (23877423329 / 1000000000000) (23877423630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (280136657267441 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33466296506 / 1000000000000) (-33466228838 / 1000000000000), orderedInterval (26468104421 / 1000000000000) (26468172089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (247509232388261 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33963439037 / 1000000000000) (33963488600 / 1000000000000), orderedInterval (-30124279903 / 1000000000000) (-30124230341 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (71737822681839 / 160000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3808278335 / 1000000000000) (3808278338 / 1000000000000), orderedInterval (-37492628705 / 1000000000000) (-37492628703 / 1000000000000)))) (orderedInterval (-5703079661 / 1000000000000) (-5703068557 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate371_chunkChecks4_2 :
    compactCertificate371.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (198430592892733 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-30145786750 / 1000000000000) (-30145786749 / 1000000000000), orderedInterval (-40655966792 / 1000000000000) (-40655966791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (168211811153813 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29361466348 / 1000000000000) (-29361466347 / 1000000000000), orderedInterval (-46466332055 / 1000000000000) (-46466332054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (105259141095239 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (27821462737 / 1000000000000) (27821462738 / 1000000000000), orderedInterval (63647588574 / 1000000000000) (63647588575 / 1000000000000)))) (orderedInterval (6367438228 / 1000000000000) (6367438280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (56608716157113 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61977707484 / 1000000000000) (61977751124 / 1000000000000), orderedInterval (-72240217239 / 1000000000000) (-72240173599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (153703676330339 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55099535324 / 1000000000000) (-55099535323 / 1000000000000), orderedInterval (-16515640575 / 1000000000000) (-16515640573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (209869229497603 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34374999307 / 1000000000000) (-34374967665 / 1000000000000), orderedInterval (35351332284 / 1000000000000) (35351363926 / 1000000000000)))) (orderedInterval (4065693667 / 1000000000000) (4065697048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (88740858904761 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74480593461 / 1000000000000) (-74480593011 / 1000000000000), orderedInterval (14182099700 / 1000000000000) (14182100150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (360726664702681 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24087992747 / 1000000000000) (-24087986802 / 1000000000000), orderedInterval (28864697064 / 1000000000000) (28864703009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (240948694481879 / 800000000000) 4 (IntervalRat.scale (485 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16965813445 / 1000000000000) (16965813446 / 1000000000000), orderedInterval (42702081110 / 1000000000000) (42702081111 / 1000000000000)))) (orderedInterval (15593609819 / 1000000000000) (15593615976 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate371_chunkChecks4 :
    compactCertificate371.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate371.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate371_chunkChecks4_0
    compactCertificate371_chunkChecks4_1 compactCertificate371_chunkChecks4_2

theorem compactCertificate371_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate371.chunkCheck r b = true :=
  compactCertificate371.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate371_chunkChecks0
    · exact compactCertificate371_chunkChecks1
    · exact compactCertificate371_chunkChecks2
    · exact compactCertificate371_chunkChecks3
    · exact compactCertificate371_chunkChecks4)

theorem compactCertificate371_coefficient0 :
    compactCertificate371.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate371_coefficient1 :
    compactCertificate371.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate371_coefficient2 :
    compactCertificate371.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate371_coefficient3 :
    compactCertificate371.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate371_coefficient4 :
    compactCertificate371.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate371_coefficients : ∀ r : Fin 5,
    compactCertificate371.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate371_coefficient0
  · exact compactCertificate371_coefficient1
  · exact compactCertificate371_coefficient2
  · exact compactCertificate371_coefficient3
  · exact compactCertificate371_coefficient4

theorem compactCertificate371_lower : (1 : ℚ) ≤ compactCertificate371.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate371, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate371_proves {t : ℝ} (ht : t ∈ compactCertificate371.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate371.proves compactCertificate371_states compactCertificate371_chunks
    compactCertificate371_coefficients compactCertificate371_lower ht

end Erdos232
