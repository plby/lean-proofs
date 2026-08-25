/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate348 : CompactCertificate where
  left := 219
  right := 220
  center := 439 / 2
  grid := fun i =>
    match i.val with
    | 0 => 70
    | 1 => 51
    | 2 => 83
    | 3 => 15
    | 4 => 40
    | 5 => 110
    | 6 => 81
    | 7 => 138
    | 8 => 102
    | 9 => 156
    | 10 => 90
    | 11 => 160
    | 12 => 150
    | 13 => 107
    | 14 => 121
    | 15 => 101
    | 16 => 89
    | 17 => 129
    | 18 => 72
    | 19 => 61
    | 20 => 38
    | 21 => 20
    | 22 => 55
    | 23 => 76
    | 24 => 32
    | 25 => 130
    | _ => 87
  point := fun i =>
    match i.val with
    | 0 => 439 / 2
    | 1 => 646730826128539 / 4000000000000
    | 2 => 209139461246587 / 800000000000
    | 3 => 188714442094673 / 4000000000000
    | 4 => 506913536348381 / 4000000000000
    | 5 => 1376368859911977 / 4000000000000
    | 6 => 1013827072697201 / 4000000000000
    | 7 => 1737209969195573 / 4000000000000
    | 8 => 1279621000610207 / 4000000000000
    | 9 => 1963267684244561 / 4000000000000
    | 10 => 1133493125989769 / 4000000000000
    | 11 => 2011403442973021 / 4000000000000
    | 12 => 1879314008817649 / 4000000000000
    | 13 => 1341167153390017 / 4000000000000
    | 14 => 1520740609045143 / 4000000000000
    | 15 => 1267834974643367 / 4000000000000
    | 16 => 1120170649674707 / 4000000000000
    | 17 => 324669115023993 / 800000000000
    | 18 => 898051858555771 / 4000000000000
    | 19 => 761288506149731 / 4000000000000
    | 20 => 476378999389793 / 4000000000000
    | 21 => 256198210236831 / 4000000000000
    | 22 => 695627978443493 / 4000000000000
    | 23 => 949820533499461 / 4000000000000
    | 24 => 401621000610207 / 4000000000000
    | 25 => 1632567070149247 / 4000000000000
    | _ => 1090479143067473 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (19642369106 / 1000000000000) (19642369107 / 1000000000000), orderedInterval (50100054410 / 1000000000000) (50100054411 / 1000000000000))
    | 1 => (orderedInterval (-48976516705 / 1000000000000) (-48976426665 / 1000000000000), orderedInterval (39378499268 / 1000000000000) (39378589308 / 1000000000000))
    | 2 => (orderedInterval (-49028815348 / 1000000000000) (-49028815328 / 1000000000000), orderedInterval (-5506948126 / 1000000000000) (-5506948106 / 1000000000000))
    | 3 => (orderedInterval (-86301052247 / 1000000000000) (-86301052246 / 1000000000000), orderedInterval (-76840685578 / 1000000000000) (-76840685577 / 1000000000000))
    | 4 => (orderedInterval (68149440293 / 1000000000000) (68149441838 / 1000000000000), orderedInterval (-19739839268 / 1000000000000) (-19739837723 / 1000000000000))
    | 5 => (orderedInterval (-27642148523 / 1000000000000) (-27642138009 / 1000000000000), orderedInterval (32995512259 / 1000000000000) (32995522773 / 1000000000000))
    | 6 => (orderedInterval (11295375525 / 1000000000000) (11295375590 / 1000000000000), orderedInterval (-48850223731 / 1000000000000) (-48850223666 / 1000000000000))
    | 7 => (orderedInterval (38276222917 / 1000000000000) (38276223173 / 1000000000000), orderedInterval (835671955 / 1000000000000) (835672211 / 1000000000000))
    | 8 => (orderedInterval (10941793498 / 1000000000000) (10941793499 / 1000000000000), orderedInterval (43229925088 / 1000000000000) (43229925089 / 1000000000000))
    | 9 => (orderedInterval (35955859918 / 1000000000000) (35955860156 / 1000000000000), orderedInterval (2021779133 / 1000000000000) (2021779371 / 1000000000000))
    | 10 => (orderedInterval (46823218730 / 1000000000000) (46823218742 / 1000000000000), orderedInterval (7276691096 / 1000000000000) (7276691109 / 1000000000000))
    | 11 => (orderedInterval (29573557223 / 1000000000000) (29573557224 / 1000000000000), orderedInterval (19755070869 / 1000000000000) (19755070870 / 1000000000000))
    | 12 => (orderedInterval (-21545524000 / 1000000000000) (-21545521485 / 1000000000000), orderedInterval (29869121385 / 1000000000000) (29869123901 / 1000000000000))
    | 13 => (orderedInterval (3204168696 / 1000000000000) (3204168700 / 1000000000000), orderedInterval (-43460953000 / 1000000000000) (-43460952996 / 1000000000000))
    | 14 => (orderedInterval (-30403176064 / 1000000000000) (-30403176063 / 1000000000000), orderedInterval (-27348809383 / 1000000000000) (-27348809382 / 1000000000000))
    | 15 => (orderedInterval (-19206218156 / 1000000000000) (-19206218155 / 1000000000000), orderedInterval (-40462274984 / 1000000000000) (-40462274983 / 1000000000000))
    | 16 => (orderedInterval (-44870742417 / 1000000000000) (-44870742415 / 1000000000000), orderedInterval (-16041590511 / 1000000000000) (-16041590509 / 1000000000000))
    | 17 => (orderedInterval (-38696418827 / 1000000000000) (-38696418814 / 1000000000000), orderedInterval (-8393131362 / 1000000000000) (-8393131349 / 1000000000000))
    | 18 => (orderedInterval (-41608158677 / 1000000000000) (-41608048326 / 1000000000000), orderedInterval (33323961954 / 1000000000000) (33324072306 / 1000000000000))
    | 19 => (orderedInterval (29251950963 / 1000000000000) (29251955128 / 1000000000000), orderedInterval (-49969617046 / 1000000000000) (-49969612881 / 1000000000000))
    | 20 => (orderedInterval (34960718230 / 1000000000000) (34960718231 / 1000000000000), orderedInterval (64065868979 / 1000000000000) (64065868980 / 1000000000000))
    | 21 => (orderedInterval (90605208943 / 1000000000000) (90605214759 / 1000000000000), orderedInterval (-42300370485 / 1000000000000) (-42300364669 / 1000000000000))
    | 22 => (orderedInterval (-57174244242 / 1000000000000) (-57174240535 / 1000000000000), orderedInterval (19957940995 / 1000000000000) (19957944702 / 1000000000000))
    | 23 => (orderedInterval (-25774232744 / 1000000000000) (-25774229829 / 1000000000000), orderedInterval (44961984049 / 1000000000000) (44961986964 / 1000000000000))
    | 24 => (orderedInterval (48722236930 / 1000000000000) (48722236931 / 1000000000000), orderedInterval (62738853141 / 1000000000000) (62738853142 / 1000000000000))
    | 25 => (orderedInterval (19617572084 / 1000000000000) (19617572085 / 1000000000000), orderedInterval (34253540884 / 1000000000000) (34253540885 / 1000000000000))
    | _ => (orderedInterval (-4158647850 / 1000000000000) (-4158647849 / 1000000000000), orderedInterval (-48136971279 / 1000000000000) (-48136971277 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (4452114587 / 1000000000000) (4452115443 / 1000000000000)
      | 1 => orderedInterval (5389629937 / 1000000000000) (5389630768 / 1000000000000)
      | 2 => orderedInterval (-916150312 / 1000000000000) (-916150291 / 1000000000000)
      | 3 => orderedInterval (1284348344 / 1000000000000) (1284348475 / 1000000000000)
      | 4 => orderedInterval (845816097 / 1000000000000) (845816170 / 1000000000000)
      | 5 => orderedInterval (1355235230 / 1000000000000) (1355235252 / 1000000000000)
      | 6 => orderedInterval (6135308709 / 1000000000000) (6135326645 / 1000000000000)
      | 7 => orderedInterval (1599376049 / 1000000000000) (1599376491 / 1000000000000)
      | _ => orderedInterval (-522918981 / 1000000000000) (-522918919 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19743311430 / 1000000000000) (19743312068 / 1000000000000)
      | 1 => orderedInterval (-3913999457 / 1000000000000) (-3913998222 / 1000000000000)
      | 2 => orderedInterval (1471694263 / 1000000000000) (1471694301 / 1000000000000)
      | 3 => orderedInterval (6326244666 / 1000000000000) (6326244943 / 1000000000000)
      | 4 => orderedInterval (-7192288214 / 1000000000000) (-7192288073 / 1000000000000)
      | 5 => orderedInterval (99182500 / 1000000000000) (99182532 / 1000000000000)
      | 6 => orderedInterval (-1866002220 / 1000000000000) (-1865983916 / 1000000000000)
      | 7 => orderedInterval (-3858522433 / 1000000000000) (-3858522069 / 1000000000000)
      | _ => orderedInterval (6205890328 / 1000000000000) (6205890414 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3546823682 / 1000000000000) (-3546823201 / 1000000000000)
      | 1 => orderedInterval (-5683859507 / 1000000000000) (-5683857604 / 1000000000000)
      | 2 => orderedInterval (4053441562 / 1000000000000) (4053441632 / 1000000000000)
      | 3 => orderedInterval (4070092953 / 1000000000000) (4070093554 / 1000000000000)
      | 4 => orderedInterval (-2917838318 / 1000000000000) (-2917838038 / 1000000000000)
      | 5 => orderedInterval (-330690446 / 1000000000000) (-330690399 / 1000000000000)
      | 6 => orderedInterval (-6041986324 / 1000000000000) (-6041967555 / 1000000000000)
      | 7 => orderedInterval (-2965872288 / 1000000000000) (-2965871939 / 1000000000000)
      | _ => orderedInterval (4227826559 / 1000000000000) (4227826686 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19442047387 / 1000000000000) (-19442047023 / 1000000000000)
      | 1 => orderedInterval (9192364625 / 1000000000000) (9192367586 / 1000000000000)
      | 2 => orderedInterval (-3053125319 / 1000000000000) (-3053125188 / 1000000000000)
      | 3 => orderedInterval (-30926251805 / 1000000000000) (-30926250480 / 1000000000000)
      | 4 => orderedInterval (19230182043 / 1000000000000) (19230182611 / 1000000000000)
      | 5 => orderedInterval (860211413 / 1000000000000) (860211486 / 1000000000000)
      | 6 => orderedInterval (3552379006 / 1000000000000) (3552398173 / 1000000000000)
      | 7 => orderedInterval (4581712090 / 1000000000000) (4581712444 / 1000000000000)
      | _ => orderedInterval (566268169 / 1000000000000) (566268366 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (2039375817 / 1000000000000) (2039376097 / 1000000000000)
      | 1 => orderedInterval (12061549615 / 1000000000000) (12061554258 / 1000000000000)
      | 2 => orderedInterval (-16872846059 / 1000000000000) (-16872845809 / 1000000000000)
      | 3 => orderedInterval (-34010190795 / 1000000000000) (-34010187846 / 1000000000000)
      | 4 => orderedInterval (11023548008 / 1000000000000) (11023549174 / 1000000000000)
      | 5 => orderedInterval (-5747092850 / 1000000000000) (-5747092735 / 1000000000000)
      | 6 => orderedInterval (6412028949 / 1000000000000) (6412048613 / 1000000000000)
      | 7 => orderedInterval (3162508466 / 1000000000000) (3162508835 / 1000000000000)
      | _ => orderedInterval (-17224619652 / 1000000000000) (-17224619338 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (19622759660 / 1000000000000) (19622780034 / 1000000000000)
    | 1 => orderedInterval (17015510863 / 1000000000000) (17015531978 / 1000000000000)
    | 2 => orderedInterval (-9135709491 / 1000000000000) (-9135686864 / 1000000000000)
    | 3 => orderedInterval (-15438307165 / 1000000000000) (-15438282025 / 1000000000000)
    | _ => orderedInterval (-39155738501 / 1000000000000) (-39155708751 / 1000000000000)

theorem compactCertificate348_stateChecks0 :
    compactCertificate348.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (439 / 2)) (orderedInterval (19642369106 / 1000000000000) (19642369107 / 1000000000000), orderedInterval (50100054410 / 1000000000000) (50100054411 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (646730826128539 / 4000000000000)) (orderedInterval (-48976516705 / 1000000000000) (-48976426665 / 1000000000000), orderedInterval (39378499268 / 1000000000000) (39378589308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (209139461246587 / 800000000000)) (orderedInterval (-49028815348 / 1000000000000) (-49028815328 / 1000000000000), orderedInterval (-5506948126 / 1000000000000) (-5506948106 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_stateChecks1 :
    compactCertificate348.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (188714442094673 / 4000000000000)) (orderedInterval (-86301052247 / 1000000000000) (-86301052246 / 1000000000000), orderedInterval (-76840685578 / 1000000000000) (-76840685577 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (506913536348381 / 4000000000000)) (orderedInterval (68149440293 / 1000000000000) (68149441838 / 1000000000000), orderedInterval (-19739839268 / 1000000000000) (-19739837723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1376368859911977 / 4000000000000)) (orderedInterval (-27642148523 / 1000000000000) (-27642138009 / 1000000000000), orderedInterval (32995512259 / 1000000000000) (32995522773 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_stateChecks2 :
    compactCertificate348.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1013827072697201 / 4000000000000)) (orderedInterval (11295375525 / 1000000000000) (11295375590 / 1000000000000), orderedInterval (-48850223731 / 1000000000000) (-48850223666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1737209969195573 / 4000000000000)) (orderedInterval (38276222917 / 1000000000000) (38276223173 / 1000000000000), orderedInterval (835671955 / 1000000000000) (835672211 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1279621000610207 / 4000000000000)) (orderedInterval (10941793498 / 1000000000000) (10941793499 / 1000000000000), orderedInterval (43229925088 / 1000000000000) (43229925089 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_stateChecks3 :
    compactCertificate348.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1963267684244561 / 4000000000000)) (orderedInterval (35955859918 / 1000000000000) (35955860156 / 1000000000000), orderedInterval (2021779133 / 1000000000000) (2021779371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1133493125989769 / 4000000000000)) (orderedInterval (46823218730 / 1000000000000) (46823218742 / 1000000000000), orderedInterval (7276691096 / 1000000000000) (7276691109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2011403442973021 / 4000000000000)) (orderedInterval (29573557223 / 1000000000000) (29573557224 / 1000000000000), orderedInterval (19755070869 / 1000000000000) (19755070870 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_stateChecks4 :
    compactCertificate348.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1879314008817649 / 4000000000000)) (orderedInterval (-21545524000 / 1000000000000) (-21545521485 / 1000000000000), orderedInterval (29869121385 / 1000000000000) (29869123901 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1341167153390017 / 4000000000000)) (orderedInterval (3204168696 / 1000000000000) (3204168700 / 1000000000000), orderedInterval (-43460953000 / 1000000000000) (-43460952996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1520740609045143 / 4000000000000)) (orderedInterval (-30403176064 / 1000000000000) (-30403176063 / 1000000000000), orderedInterval (-27348809383 / 1000000000000) (-27348809382 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_stateChecks5 :
    compactCertificate348.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1267834974643367 / 4000000000000)) (orderedInterval (-19206218156 / 1000000000000) (-19206218155 / 1000000000000), orderedInterval (-40462274984 / 1000000000000) (-40462274983 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1120170649674707 / 4000000000000)) (orderedInterval (-44870742417 / 1000000000000) (-44870742415 / 1000000000000), orderedInterval (-16041590511 / 1000000000000) (-16041590509 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (324669115023993 / 800000000000)) (orderedInterval (-38696418827 / 1000000000000) (-38696418814 / 1000000000000), orderedInterval (-8393131362 / 1000000000000) (-8393131349 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_stateChecks6 :
    compactCertificate348.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (898051858555771 / 4000000000000)) (orderedInterval (-41608158677 / 1000000000000) (-41608048326 / 1000000000000), orderedInterval (33323961954 / 1000000000000) (33324072306 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (761288506149731 / 4000000000000)) (orderedInterval (29251950963 / 1000000000000) (29251955128 / 1000000000000), orderedInterval (-49969617046 / 1000000000000) (-49969612881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (476378999389793 / 4000000000000)) (orderedInterval (34960718230 / 1000000000000) (34960718231 / 1000000000000), orderedInterval (64065868979 / 1000000000000) (64065868980 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_stateChecks7 :
    compactCertificate348.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (256198210236831 / 4000000000000)) (orderedInterval (90605208943 / 1000000000000) (90605214759 / 1000000000000), orderedInterval (-42300370485 / 1000000000000) (-42300364669 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (695627978443493 / 4000000000000)) (orderedInterval (-57174244242 / 1000000000000) (-57174240535 / 1000000000000), orderedInterval (19957940995 / 1000000000000) (19957944702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (949820533499461 / 4000000000000)) (orderedInterval (-25774232744 / 1000000000000) (-25774229829 / 1000000000000), orderedInterval (44961984049 / 1000000000000) (44961986964 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_stateChecks8 :
    compactCertificate348.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (401621000610207 / 4000000000000)) (orderedInterval (48722236930 / 1000000000000) (48722236931 / 1000000000000), orderedInterval (62738853141 / 1000000000000) (62738853142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1632567070149247 / 4000000000000)) (orderedInterval (19617572084 / 1000000000000) (19617572085 / 1000000000000), orderedInterval (34253540884 / 1000000000000) (34253540885 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1090479143067473 / 4000000000000)) (orderedInterval (-4158647850 / 1000000000000) (-4158647849 / 1000000000000), orderedInterval (-48136971279 / 1000000000000) (-48136971277 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_states : ∀ j,
    BesselStateValid (compactCertificate348.point j) (compactCertificate348.state j) :=
  compactCertificate348.statesValid_of_checks3 compactCertificate348_stateChecks0
    compactCertificate348_stateChecks1 compactCertificate348_stateChecks2
    compactCertificate348_stateChecks3 compactCertificate348_stateChecks4
    compactCertificate348_stateChecks5 compactCertificate348_stateChecks6
    compactCertificate348_stateChecks7 compactCertificate348_stateChecks8

theorem compactCertificate348_chunkChecks0_0 :
    compactCertificate348.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (439 / 2) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19642369106 / 1000000000000) (19642369107 / 1000000000000), orderedInterval (50100054410 / 1000000000000) (50100054411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (646730826128539 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48976516705 / 1000000000000) (-48976426665 / 1000000000000), orderedInterval (39378499268 / 1000000000000) (39378589308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (209139461246587 / 800000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49028815348 / 1000000000000) (-49028815328 / 1000000000000), orderedInterval (-5506948126 / 1000000000000) (-5506948106 / 1000000000000)))) (orderedInterval (4452114587 / 1000000000000) (4452115443 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (188714442094673 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86301052247 / 1000000000000) (-86301052246 / 1000000000000), orderedInterval (-76840685578 / 1000000000000) (-76840685577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (506913536348381 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68149440293 / 1000000000000) (68149441838 / 1000000000000), orderedInterval (-19739839268 / 1000000000000) (-19739837723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1376368859911977 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27642148523 / 1000000000000) (-27642138009 / 1000000000000), orderedInterval (32995512259 / 1000000000000) (32995522773 / 1000000000000)))) (orderedInterval (5389629937 / 1000000000000) (5389630768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1013827072697201 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11295375525 / 1000000000000) (11295375590 / 1000000000000), orderedInterval (-48850223731 / 1000000000000) (-48850223666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1737209969195573 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38276222917 / 1000000000000) (38276223173 / 1000000000000), orderedInterval (835671955 / 1000000000000) (835672211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1279621000610207 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10941793498 / 1000000000000) (10941793499 / 1000000000000), orderedInterval (43229925088 / 1000000000000) (43229925089 / 1000000000000)))) (orderedInterval (-916150312 / 1000000000000) (-916150291 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks0_1 :
    compactCertificate348.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1963267684244561 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35955859918 / 1000000000000) (35955860156 / 1000000000000), orderedInterval (2021779133 / 1000000000000) (2021779371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1133493125989769 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46823218730 / 1000000000000) (46823218742 / 1000000000000), orderedInterval (7276691096 / 1000000000000) (7276691109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2011403442973021 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29573557223 / 1000000000000) (29573557224 / 1000000000000), orderedInterval (19755070869 / 1000000000000) (19755070870 / 1000000000000)))) (orderedInterval (1284348344 / 1000000000000) (1284348475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1879314008817649 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21545524000 / 1000000000000) (-21545521485 / 1000000000000), orderedInterval (29869121385 / 1000000000000) (29869123901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1341167153390017 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3204168696 / 1000000000000) (3204168700 / 1000000000000), orderedInterval (-43460953000 / 1000000000000) (-43460952996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1520740609045143 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30403176064 / 1000000000000) (-30403176063 / 1000000000000), orderedInterval (-27348809383 / 1000000000000) (-27348809382 / 1000000000000)))) (orderedInterval (845816097 / 1000000000000) (845816170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1267834974643367 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19206218156 / 1000000000000) (-19206218155 / 1000000000000), orderedInterval (-40462274984 / 1000000000000) (-40462274983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1120170649674707 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44870742417 / 1000000000000) (-44870742415 / 1000000000000), orderedInterval (-16041590511 / 1000000000000) (-16041590509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (324669115023993 / 800000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38696418827 / 1000000000000) (-38696418814 / 1000000000000), orderedInterval (-8393131362 / 1000000000000) (-8393131349 / 1000000000000)))) (orderedInterval (1355235230 / 1000000000000) (1355235252 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks0_2 :
    compactCertificate348.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (898051858555771 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41608158677 / 1000000000000) (-41608048326 / 1000000000000), orderedInterval (33323961954 / 1000000000000) (33324072306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (761288506149731 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29251950963 / 1000000000000) (29251955128 / 1000000000000), orderedInterval (-49969617046 / 1000000000000) (-49969612881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (476378999389793 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34960718230 / 1000000000000) (34960718231 / 1000000000000), orderedInterval (64065868979 / 1000000000000) (64065868980 / 1000000000000)))) (orderedInterval (6135308709 / 1000000000000) (6135326645 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (256198210236831 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90605208943 / 1000000000000) (90605214759 / 1000000000000), orderedInterval (-42300370485 / 1000000000000) (-42300364669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (695627978443493 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-57174244242 / 1000000000000) (-57174240535 / 1000000000000), orderedInterval (19957940995 / 1000000000000) (19957944702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (949820533499461 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25774232744 / 1000000000000) (-25774229829 / 1000000000000), orderedInterval (44961984049 / 1000000000000) (44961986964 / 1000000000000)))) (orderedInterval (1599376049 / 1000000000000) (1599376491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (401621000610207 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48722236930 / 1000000000000) (48722236931 / 1000000000000), orderedInterval (62738853141 / 1000000000000) (62738853142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1632567070149247 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19617572084 / 1000000000000) (19617572085 / 1000000000000), orderedInterval (34253540884 / 1000000000000) (34253540885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1090479143067473 / 4000000000000) 0 (IntervalRat.scale (439 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4158647850 / 1000000000000) (-4158647849 / 1000000000000), orderedInterval (-48136971279 / 1000000000000) (-48136971277 / 1000000000000)))) (orderedInterval (-522918981 / 1000000000000) (-522918919 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks0 :
    compactCertificate348.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate348.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate348_chunkChecks0_0
    compactCertificate348_chunkChecks0_1 compactCertificate348_chunkChecks0_2

theorem compactCertificate348_chunkChecks1_0 :
    compactCertificate348.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (439 / 2) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19642369106 / 1000000000000) (19642369107 / 1000000000000), orderedInterval (50100054410 / 1000000000000) (50100054411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (646730826128539 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48976516705 / 1000000000000) (-48976426665 / 1000000000000), orderedInterval (39378499268 / 1000000000000) (39378589308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (209139461246587 / 800000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49028815348 / 1000000000000) (-49028815328 / 1000000000000), orderedInterval (-5506948126 / 1000000000000) (-5506948106 / 1000000000000)))) (orderedInterval (19743311430 / 1000000000000) (19743312068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (188714442094673 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86301052247 / 1000000000000) (-86301052246 / 1000000000000), orderedInterval (-76840685578 / 1000000000000) (-76840685577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (506913536348381 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68149440293 / 1000000000000) (68149441838 / 1000000000000), orderedInterval (-19739839268 / 1000000000000) (-19739837723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1376368859911977 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27642148523 / 1000000000000) (-27642138009 / 1000000000000), orderedInterval (32995512259 / 1000000000000) (32995522773 / 1000000000000)))) (orderedInterval (-3913999457 / 1000000000000) (-3913998222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1013827072697201 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11295375525 / 1000000000000) (11295375590 / 1000000000000), orderedInterval (-48850223731 / 1000000000000) (-48850223666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1737209969195573 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38276222917 / 1000000000000) (38276223173 / 1000000000000), orderedInterval (835671955 / 1000000000000) (835672211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1279621000610207 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10941793498 / 1000000000000) (10941793499 / 1000000000000), orderedInterval (43229925088 / 1000000000000) (43229925089 / 1000000000000)))) (orderedInterval (1471694263 / 1000000000000) (1471694301 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks1_1 :
    compactCertificate348.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1963267684244561 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35955859918 / 1000000000000) (35955860156 / 1000000000000), orderedInterval (2021779133 / 1000000000000) (2021779371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1133493125989769 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46823218730 / 1000000000000) (46823218742 / 1000000000000), orderedInterval (7276691096 / 1000000000000) (7276691109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2011403442973021 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29573557223 / 1000000000000) (29573557224 / 1000000000000), orderedInterval (19755070869 / 1000000000000) (19755070870 / 1000000000000)))) (orderedInterval (6326244666 / 1000000000000) (6326244943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1879314008817649 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21545524000 / 1000000000000) (-21545521485 / 1000000000000), orderedInterval (29869121385 / 1000000000000) (29869123901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1341167153390017 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3204168696 / 1000000000000) (3204168700 / 1000000000000), orderedInterval (-43460953000 / 1000000000000) (-43460952996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1520740609045143 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30403176064 / 1000000000000) (-30403176063 / 1000000000000), orderedInterval (-27348809383 / 1000000000000) (-27348809382 / 1000000000000)))) (orderedInterval (-7192288214 / 1000000000000) (-7192288073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1267834974643367 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19206218156 / 1000000000000) (-19206218155 / 1000000000000), orderedInterval (-40462274984 / 1000000000000) (-40462274983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1120170649674707 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44870742417 / 1000000000000) (-44870742415 / 1000000000000), orderedInterval (-16041590511 / 1000000000000) (-16041590509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (324669115023993 / 800000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38696418827 / 1000000000000) (-38696418814 / 1000000000000), orderedInterval (-8393131362 / 1000000000000) (-8393131349 / 1000000000000)))) (orderedInterval (99182500 / 1000000000000) (99182532 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks1_2 :
    compactCertificate348.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (898051858555771 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41608158677 / 1000000000000) (-41608048326 / 1000000000000), orderedInterval (33323961954 / 1000000000000) (33324072306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (761288506149731 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29251950963 / 1000000000000) (29251955128 / 1000000000000), orderedInterval (-49969617046 / 1000000000000) (-49969612881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (476378999389793 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34960718230 / 1000000000000) (34960718231 / 1000000000000), orderedInterval (64065868979 / 1000000000000) (64065868980 / 1000000000000)))) (orderedInterval (-1866002220 / 1000000000000) (-1865983916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (256198210236831 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90605208943 / 1000000000000) (90605214759 / 1000000000000), orderedInterval (-42300370485 / 1000000000000) (-42300364669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (695627978443493 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-57174244242 / 1000000000000) (-57174240535 / 1000000000000), orderedInterval (19957940995 / 1000000000000) (19957944702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (949820533499461 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25774232744 / 1000000000000) (-25774229829 / 1000000000000), orderedInterval (44961984049 / 1000000000000) (44961986964 / 1000000000000)))) (orderedInterval (-3858522433 / 1000000000000) (-3858522069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (401621000610207 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48722236930 / 1000000000000) (48722236931 / 1000000000000), orderedInterval (62738853141 / 1000000000000) (62738853142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1632567070149247 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19617572084 / 1000000000000) (19617572085 / 1000000000000), orderedInterval (34253540884 / 1000000000000) (34253540885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1090479143067473 / 4000000000000) 1 (IntervalRat.scale (439 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4158647850 / 1000000000000) (-4158647849 / 1000000000000), orderedInterval (-48136971279 / 1000000000000) (-48136971277 / 1000000000000)))) (orderedInterval (6205890328 / 1000000000000) (6205890414 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks1 :
    compactCertificate348.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate348.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate348_chunkChecks1_0
    compactCertificate348_chunkChecks1_1 compactCertificate348_chunkChecks1_2

theorem compactCertificate348_chunkChecks2_0 :
    compactCertificate348.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (439 / 2) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19642369106 / 1000000000000) (19642369107 / 1000000000000), orderedInterval (50100054410 / 1000000000000) (50100054411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (646730826128539 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48976516705 / 1000000000000) (-48976426665 / 1000000000000), orderedInterval (39378499268 / 1000000000000) (39378589308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (209139461246587 / 800000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49028815348 / 1000000000000) (-49028815328 / 1000000000000), orderedInterval (-5506948126 / 1000000000000) (-5506948106 / 1000000000000)))) (orderedInterval (-3546823682 / 1000000000000) (-3546823201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (188714442094673 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86301052247 / 1000000000000) (-86301052246 / 1000000000000), orderedInterval (-76840685578 / 1000000000000) (-76840685577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (506913536348381 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68149440293 / 1000000000000) (68149441838 / 1000000000000), orderedInterval (-19739839268 / 1000000000000) (-19739837723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1376368859911977 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27642148523 / 1000000000000) (-27642138009 / 1000000000000), orderedInterval (32995512259 / 1000000000000) (32995522773 / 1000000000000)))) (orderedInterval (-5683859507 / 1000000000000) (-5683857604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1013827072697201 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11295375525 / 1000000000000) (11295375590 / 1000000000000), orderedInterval (-48850223731 / 1000000000000) (-48850223666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1737209969195573 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38276222917 / 1000000000000) (38276223173 / 1000000000000), orderedInterval (835671955 / 1000000000000) (835672211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1279621000610207 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10941793498 / 1000000000000) (10941793499 / 1000000000000), orderedInterval (43229925088 / 1000000000000) (43229925089 / 1000000000000)))) (orderedInterval (4053441562 / 1000000000000) (4053441632 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks2_1 :
    compactCertificate348.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1963267684244561 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35955859918 / 1000000000000) (35955860156 / 1000000000000), orderedInterval (2021779133 / 1000000000000) (2021779371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1133493125989769 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46823218730 / 1000000000000) (46823218742 / 1000000000000), orderedInterval (7276691096 / 1000000000000) (7276691109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2011403442973021 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29573557223 / 1000000000000) (29573557224 / 1000000000000), orderedInterval (19755070869 / 1000000000000) (19755070870 / 1000000000000)))) (orderedInterval (4070092953 / 1000000000000) (4070093554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1879314008817649 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21545524000 / 1000000000000) (-21545521485 / 1000000000000), orderedInterval (29869121385 / 1000000000000) (29869123901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1341167153390017 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3204168696 / 1000000000000) (3204168700 / 1000000000000), orderedInterval (-43460953000 / 1000000000000) (-43460952996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1520740609045143 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30403176064 / 1000000000000) (-30403176063 / 1000000000000), orderedInterval (-27348809383 / 1000000000000) (-27348809382 / 1000000000000)))) (orderedInterval (-2917838318 / 1000000000000) (-2917838038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1267834974643367 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19206218156 / 1000000000000) (-19206218155 / 1000000000000), orderedInterval (-40462274984 / 1000000000000) (-40462274983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1120170649674707 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44870742417 / 1000000000000) (-44870742415 / 1000000000000), orderedInterval (-16041590511 / 1000000000000) (-16041590509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (324669115023993 / 800000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38696418827 / 1000000000000) (-38696418814 / 1000000000000), orderedInterval (-8393131362 / 1000000000000) (-8393131349 / 1000000000000)))) (orderedInterval (-330690446 / 1000000000000) (-330690399 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks2_2 :
    compactCertificate348.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (898051858555771 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41608158677 / 1000000000000) (-41608048326 / 1000000000000), orderedInterval (33323961954 / 1000000000000) (33324072306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (761288506149731 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29251950963 / 1000000000000) (29251955128 / 1000000000000), orderedInterval (-49969617046 / 1000000000000) (-49969612881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (476378999389793 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34960718230 / 1000000000000) (34960718231 / 1000000000000), orderedInterval (64065868979 / 1000000000000) (64065868980 / 1000000000000)))) (orderedInterval (-6041986324 / 1000000000000) (-6041967555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (256198210236831 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90605208943 / 1000000000000) (90605214759 / 1000000000000), orderedInterval (-42300370485 / 1000000000000) (-42300364669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (695627978443493 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-57174244242 / 1000000000000) (-57174240535 / 1000000000000), orderedInterval (19957940995 / 1000000000000) (19957944702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (949820533499461 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25774232744 / 1000000000000) (-25774229829 / 1000000000000), orderedInterval (44961984049 / 1000000000000) (44961986964 / 1000000000000)))) (orderedInterval (-2965872288 / 1000000000000) (-2965871939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (401621000610207 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48722236930 / 1000000000000) (48722236931 / 1000000000000), orderedInterval (62738853141 / 1000000000000) (62738853142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1632567070149247 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19617572084 / 1000000000000) (19617572085 / 1000000000000), orderedInterval (34253540884 / 1000000000000) (34253540885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1090479143067473 / 4000000000000) 2 (IntervalRat.scale (439 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4158647850 / 1000000000000) (-4158647849 / 1000000000000), orderedInterval (-48136971279 / 1000000000000) (-48136971277 / 1000000000000)))) (orderedInterval (4227826559 / 1000000000000) (4227826686 / 1000000000000))) = true
  rfl'

theorem compactCertificate348_chunkChecks2 :
    compactCertificate348.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate348.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate348_chunkChecks2_0
    compactCertificate348_chunkChecks2_1 compactCertificate348_chunkChecks2_2

theorem compactCertificate348_chunkChecks3_0 :
    compactCertificate348.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (439 / 2) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19642369106 / 1000000000000) (19642369107 / 1000000000000), orderedInterval (50100054410 / 1000000000000) (50100054411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (646730826128539 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48976516705 / 1000000000000) (-48976426665 / 1000000000000), orderedInterval (39378499268 / 1000000000000) (39378589308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (209139461246587 / 800000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49028815348 / 1000000000000) (-49028815328 / 1000000000000), orderedInterval (-5506948126 / 1000000000000) (-5506948106 / 1000000000000)))) (orderedInterval (-19442047387 / 1000000000000) (-19442047023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (188714442094673 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86301052247 / 1000000000000) (-86301052246 / 1000000000000), orderedInterval (-76840685578 / 1000000000000) (-76840685577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (506913536348381 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68149440293 / 1000000000000) (68149441838 / 1000000000000), orderedInterval (-19739839268 / 1000000000000) (-19739837723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1376368859911977 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27642148523 / 1000000000000) (-27642138009 / 1000000000000), orderedInterval (32995512259 / 1000000000000) (32995522773 / 1000000000000)))) (orderedInterval (9192364625 / 1000000000000) (9192367586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1013827072697201 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11295375525 / 1000000000000) (11295375590 / 1000000000000), orderedInterval (-48850223731 / 1000000000000) (-48850223666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1737209969195573 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38276222917 / 1000000000000) (38276223173 / 1000000000000), orderedInterval (835671955 / 1000000000000) (835672211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1279621000610207 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10941793498 / 1000000000000) (10941793499 / 1000000000000), orderedInterval (43229925088 / 1000000000000) (43229925089 / 1000000000000)))) (orderedInterval (-3053125319 / 1000000000000) (-3053125188 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate348_chunkChecks3_1 :
    compactCertificate348.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1963267684244561 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35955859918 / 1000000000000) (35955860156 / 1000000000000), orderedInterval (2021779133 / 1000000000000) (2021779371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1133493125989769 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46823218730 / 1000000000000) (46823218742 / 1000000000000), orderedInterval (7276691096 / 1000000000000) (7276691109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2011403442973021 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29573557223 / 1000000000000) (29573557224 / 1000000000000), orderedInterval (19755070869 / 1000000000000) (19755070870 / 1000000000000)))) (orderedInterval (-30926251805 / 1000000000000) (-30926250480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1879314008817649 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21545524000 / 1000000000000) (-21545521485 / 1000000000000), orderedInterval (29869121385 / 1000000000000) (29869123901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1341167153390017 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3204168696 / 1000000000000) (3204168700 / 1000000000000), orderedInterval (-43460953000 / 1000000000000) (-43460952996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1520740609045143 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30403176064 / 1000000000000) (-30403176063 / 1000000000000), orderedInterval (-27348809383 / 1000000000000) (-27348809382 / 1000000000000)))) (orderedInterval (19230182043 / 1000000000000) (19230182611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1267834974643367 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19206218156 / 1000000000000) (-19206218155 / 1000000000000), orderedInterval (-40462274984 / 1000000000000) (-40462274983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1120170649674707 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44870742417 / 1000000000000) (-44870742415 / 1000000000000), orderedInterval (-16041590511 / 1000000000000) (-16041590509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (324669115023993 / 800000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38696418827 / 1000000000000) (-38696418814 / 1000000000000), orderedInterval (-8393131362 / 1000000000000) (-8393131349 / 1000000000000)))) (orderedInterval (860211413 / 1000000000000) (860211486 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate348_chunkChecks3_2 :
    compactCertificate348.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (898051858555771 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41608158677 / 1000000000000) (-41608048326 / 1000000000000), orderedInterval (33323961954 / 1000000000000) (33324072306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (761288506149731 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29251950963 / 1000000000000) (29251955128 / 1000000000000), orderedInterval (-49969617046 / 1000000000000) (-49969612881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (476378999389793 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34960718230 / 1000000000000) (34960718231 / 1000000000000), orderedInterval (64065868979 / 1000000000000) (64065868980 / 1000000000000)))) (orderedInterval (3552379006 / 1000000000000) (3552398173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (256198210236831 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90605208943 / 1000000000000) (90605214759 / 1000000000000), orderedInterval (-42300370485 / 1000000000000) (-42300364669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (695627978443493 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-57174244242 / 1000000000000) (-57174240535 / 1000000000000), orderedInterval (19957940995 / 1000000000000) (19957944702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (949820533499461 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25774232744 / 1000000000000) (-25774229829 / 1000000000000), orderedInterval (44961984049 / 1000000000000) (44961986964 / 1000000000000)))) (orderedInterval (4581712090 / 1000000000000) (4581712444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (401621000610207 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48722236930 / 1000000000000) (48722236931 / 1000000000000), orderedInterval (62738853141 / 1000000000000) (62738853142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1632567070149247 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19617572084 / 1000000000000) (19617572085 / 1000000000000), orderedInterval (34253540884 / 1000000000000) (34253540885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1090479143067473 / 4000000000000) 3 (IntervalRat.scale (439 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4158647850 / 1000000000000) (-4158647849 / 1000000000000), orderedInterval (-48136971279 / 1000000000000) (-48136971277 / 1000000000000)))) (orderedInterval (566268169 / 1000000000000) (566268366 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate348_chunkChecks3 :
    compactCertificate348.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate348.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate348_chunkChecks3_0
    compactCertificate348_chunkChecks3_1 compactCertificate348_chunkChecks3_2

theorem compactCertificate348_chunkChecks4_0 :
    compactCertificate348.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (439 / 2) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19642369106 / 1000000000000) (19642369107 / 1000000000000), orderedInterval (50100054410 / 1000000000000) (50100054411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (646730826128539 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48976516705 / 1000000000000) (-48976426665 / 1000000000000), orderedInterval (39378499268 / 1000000000000) (39378589308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (209139461246587 / 800000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49028815348 / 1000000000000) (-49028815328 / 1000000000000), orderedInterval (-5506948126 / 1000000000000) (-5506948106 / 1000000000000)))) (orderedInterval (2039375817 / 1000000000000) (2039376097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (188714442094673 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-86301052247 / 1000000000000) (-86301052246 / 1000000000000), orderedInterval (-76840685578 / 1000000000000) (-76840685577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (506913536348381 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68149440293 / 1000000000000) (68149441838 / 1000000000000), orderedInterval (-19739839268 / 1000000000000) (-19739837723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1376368859911977 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27642148523 / 1000000000000) (-27642138009 / 1000000000000), orderedInterval (32995512259 / 1000000000000) (32995522773 / 1000000000000)))) (orderedInterval (12061549615 / 1000000000000) (12061554258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1013827072697201 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11295375525 / 1000000000000) (11295375590 / 1000000000000), orderedInterval (-48850223731 / 1000000000000) (-48850223666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1737209969195573 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38276222917 / 1000000000000) (38276223173 / 1000000000000), orderedInterval (835671955 / 1000000000000) (835672211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1279621000610207 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10941793498 / 1000000000000) (10941793499 / 1000000000000), orderedInterval (43229925088 / 1000000000000) (43229925089 / 1000000000000)))) (orderedInterval (-16872846059 / 1000000000000) (-16872845809 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate348_chunkChecks4_1 :
    compactCertificate348.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1963267684244561 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35955859918 / 1000000000000) (35955860156 / 1000000000000), orderedInterval (2021779133 / 1000000000000) (2021779371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1133493125989769 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46823218730 / 1000000000000) (46823218742 / 1000000000000), orderedInterval (7276691096 / 1000000000000) (7276691109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2011403442973021 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29573557223 / 1000000000000) (29573557224 / 1000000000000), orderedInterval (19755070869 / 1000000000000) (19755070870 / 1000000000000)))) (orderedInterval (-34010190795 / 1000000000000) (-34010187846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1879314008817649 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21545524000 / 1000000000000) (-21545521485 / 1000000000000), orderedInterval (29869121385 / 1000000000000) (29869123901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1341167153390017 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3204168696 / 1000000000000) (3204168700 / 1000000000000), orderedInterval (-43460953000 / 1000000000000) (-43460952996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1520740609045143 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30403176064 / 1000000000000) (-30403176063 / 1000000000000), orderedInterval (-27348809383 / 1000000000000) (-27348809382 / 1000000000000)))) (orderedInterval (11023548008 / 1000000000000) (11023549174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1267834974643367 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19206218156 / 1000000000000) (-19206218155 / 1000000000000), orderedInterval (-40462274984 / 1000000000000) (-40462274983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1120170649674707 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44870742417 / 1000000000000) (-44870742415 / 1000000000000), orderedInterval (-16041590511 / 1000000000000) (-16041590509 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (324669115023993 / 800000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38696418827 / 1000000000000) (-38696418814 / 1000000000000), orderedInterval (-8393131362 / 1000000000000) (-8393131349 / 1000000000000)))) (orderedInterval (-5747092850 / 1000000000000) (-5747092735 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate348_chunkChecks4_2 :
    compactCertificate348.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (898051858555771 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41608158677 / 1000000000000) (-41608048326 / 1000000000000), orderedInterval (33323961954 / 1000000000000) (33324072306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (761288506149731 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29251950963 / 1000000000000) (29251955128 / 1000000000000), orderedInterval (-49969617046 / 1000000000000) (-49969612881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (476378999389793 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34960718230 / 1000000000000) (34960718231 / 1000000000000), orderedInterval (64065868979 / 1000000000000) (64065868980 / 1000000000000)))) (orderedInterval (6412028949 / 1000000000000) (6412048613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (256198210236831 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90605208943 / 1000000000000) (90605214759 / 1000000000000), orderedInterval (-42300370485 / 1000000000000) (-42300364669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (695627978443493 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-57174244242 / 1000000000000) (-57174240535 / 1000000000000), orderedInterval (19957940995 / 1000000000000) (19957944702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (949820533499461 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25774232744 / 1000000000000) (-25774229829 / 1000000000000), orderedInterval (44961984049 / 1000000000000) (44961986964 / 1000000000000)))) (orderedInterval (3162508466 / 1000000000000) (3162508835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (401621000610207 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48722236930 / 1000000000000) (48722236931 / 1000000000000), orderedInterval (62738853141 / 1000000000000) (62738853142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1632567070149247 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19617572084 / 1000000000000) (19617572085 / 1000000000000), orderedInterval (34253540884 / 1000000000000) (34253540885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1090479143067473 / 4000000000000) 4 (IntervalRat.scale (439 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4158647850 / 1000000000000) (-4158647849 / 1000000000000), orderedInterval (-48136971279 / 1000000000000) (-48136971277 / 1000000000000)))) (orderedInterval (-17224619652 / 1000000000000) (-17224619338 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate348_chunkChecks4 :
    compactCertificate348.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate348.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate348_chunkChecks4_0
    compactCertificate348_chunkChecks4_1 compactCertificate348_chunkChecks4_2

theorem compactCertificate348_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate348.chunkCheck r b = true :=
  compactCertificate348.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate348_chunkChecks0
    · exact compactCertificate348_chunkChecks1
    · exact compactCertificate348_chunkChecks2
    · exact compactCertificate348_chunkChecks3
    · exact compactCertificate348_chunkChecks4)

theorem compactCertificate348_coefficient0 :
    compactCertificate348.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate348_coefficient1 :
    compactCertificate348.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate348_coefficient2 :
    compactCertificate348.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate348_coefficient3 :
    compactCertificate348.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate348_coefficient4 :
    compactCertificate348.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate348_coefficients : ∀ r : Fin 5,
    compactCertificate348.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate348_coefficient0
  · exact compactCertificate348_coefficient1
  · exact compactCertificate348_coefficient2
  · exact compactCertificate348_coefficient3
  · exact compactCertificate348_coefficient4

theorem compactCertificate348_lower : (1 : ℚ) ≤ compactCertificate348.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate348, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate348_proves {t : ℝ} (ht : t ∈ compactCertificate348.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate348.proves compactCertificate348_states compactCertificate348_chunks
    compactCertificate348_coefficients compactCertificate348_lower ht

end Erdos232
