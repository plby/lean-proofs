/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate475 : CompactCertificate where
  left := 346
  right := 347
  center := 693 / 2
  grid := fun i =>
    match i.val with
    | 0 => 110
    | 1 => 81
    | 2 => 131
    | 3 => 24
    | 4 => 64
    | 5 => 173
    | 6 => 127
    | 7 => 218
    | 8 => 161
    | 9 => 247
    | 10 => 142
    | 11 => 253
    | 12 => 236
    | 13 => 169
    | 14 => 191
    | 15 => 159
    | 16 => 141
    | 17 => 204
    | 18 => 113
    | 19 => 96
    | 20 => 60
    | 21 => 32
    | 22 => 87
    | 23 => 119
    | 24 => 50
    | 25 => 205
    | _ => 137
  point := fun i =>
    match i.val with
    | 0 => 693 / 2
    | 1 => 1020921326895393 / 4000000000000
    | 2 => 330144980965569 / 800000000000
    | 3 => 297902296974051 / 4000000000000
    | 4 => 800207473096647 / 4000000000000
    | 5 => 2172718951979499 / 4000000000000
    | 6 => 1600414946193987 / 4000000000000
    | 7 => 2742338288502351 / 4000000000000
    | 8 => 2019993971350509 / 4000000000000
    | 9 => 3099190216814307 / 4000000000000
    | 10 => 1789318305947403 / 4000000000000
    | 11 => 3175176733440327 / 4000000000000
    | 12 => 2966661977472963 / 4000000000000
    | 13 => 2117149971068979 / 4000000000000
    | 14 => 2400622419289941 / 4000000000000
    | 15 => 2001388695735429 / 4000000000000
    | 16 => 1768287608712009 / 4000000000000
    | 17 => 512518671324891 / 800000000000
    | 18 => 1417653617264577 / 4000000000000
    | 19 => 1201760671439097 / 4000000000000
    | 20 => 752006028649491 / 4000000000000
    | 21 => 404431343266797 / 4000000000000
    | 22 => 1098109770071391 / 4000000000000
    | 23 => 1499375010740607 / 4000000000000
    | 24 => 633993971350509 / 4000000000000
    | 25 => 2577150295246989 / 4000000000000
    | _ => 1721416961607651 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (42449847908 / 1000000000000) (42449849017 / 1000000000000), orderedInterval (-6002217226 / 1000000000000) (-6002216116 / 1000000000000))
    | 1 => (orderedInterval (-49927807555 / 1000000000000) (-49927807483 / 1000000000000), orderedInterval (-1128723473 / 1000000000000) (-1128723401 / 1000000000000))
    | 2 => (orderedInterval (-36936998988 / 1000000000000) (-36936984390 / 1000000000000), orderedInterval (13397672652 / 1000000000000) (13397687250 / 1000000000000))
    | 3 => (orderedInterval (-12803385032 / 1000000000000) (-12803384966 / 1000000000000), orderedInterval (91651737890 / 1000000000000) (91651737956 / 1000000000000))
    | 4 => (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))
    | 5 => (orderedInterval (-15485465635 / 1000000000000) (-15485465634 / 1000000000000), orderedInterval (-30518102170 / 1000000000000) (-30518102169 / 1000000000000))
    | 6 => (orderedInterval (-37661662840 / 1000000000000) (-37661650531 / 1000000000000), orderedInterval (13189942950 / 1000000000000) (13189955258 / 1000000000000))
    | 7 => (orderedInterval (30401743424 / 1000000000000) (30401744149 / 1000000000000), orderedInterval (2054656731 / 1000000000000) (2054657456 / 1000000000000))
    | 8 => (orderedInterval (453525364 / 1000000000000) (453525365 / 1000000000000), orderedInterval (-35503011020 / 1000000000000) (-35503011019 / 1000000000000))
    | 9 => (orderedInterval (10913706035 / 1000000000000) (10913706049 / 1000000000000), orderedInterval (-26512714860 / 1000000000000) (-26512714846 / 1000000000000))
    | 10 => (orderedInterval (34167684186 / 1000000000000) (34167724263 / 1000000000000), orderedInterval (-16029563620 / 1000000000000) (-16029523543 / 1000000000000))
    | 11 => (orderedInterval (6828338626 / 1000000000000) (6828338627 / 1000000000000), orderedInterval (-27488295471 / 1000000000000) (-27488295469 / 1000000000000))
    | 12 => (orderedInterval (25190003320 / 1000000000000) (25190003322 / 1000000000000), orderedInterval (14943924818 / 1000000000000) (14943924820 / 1000000000000))
    | 13 => (orderedInterval (26203608772 / 1000000000000) (26203628471 / 1000000000000), orderedInterval (-22743844117 / 1000000000000) (-22743824417 / 1000000000000))
    | 14 => (orderedInterval (-25443362373 / 1000000000000) (-25443362372 / 1000000000000), orderedInterval (-20310873080 / 1000000000000) (-20310873079 / 1000000000000))
    | 15 => (orderedInterval (-35628503480 / 1000000000000) (-35628502527 / 1000000000000), orderedInterval (1757586830 / 1000000000000) (1757587783 / 1000000000000))
    | 16 => (orderedInterval (4073357491 / 1000000000000) (4073357494 / 1000000000000), orderedInterval (-37733781782 / 1000000000000) (-37733781779 / 1000000000000))
    | 17 => (orderedInterval (16440227406 / 1000000000000) (16440227407 / 1000000000000), orderedInterval (26883837931 / 1000000000000) (26883837932 / 1000000000000))
    | 18 => (orderedInterval (-8356918500 / 1000000000000) (-8356918499 / 1000000000000), orderedInterval (-41538502756 / 1000000000000) (-41538502755 / 1000000000000))
    | 19 => (orderedInterval (-16549087224 / 1000000000000) (-16549086902 / 1000000000000), orderedInterval (42982014872 / 1000000000000) (42982015194 / 1000000000000))
    | 20 => (orderedInterval (16677936171 / 1000000000000) (16677936172 / 1000000000000), orderedInterval (55706022849 / 1000000000000) (55706022850 / 1000000000000))
    | 21 => (orderedInterval (77610317695 / 1000000000000) (77610317697 / 1000000000000), orderedInterval (16139276957 / 1000000000000) (16139276958 / 1000000000000))
    | 22 => (orderedInterval (-43910692915 / 1000000000000) (-43910677413 / 1000000000000), orderedInterval (19849009109 / 1000000000000) (19849024611 / 1000000000000))
    | 23 => (orderedInterval (-40318661036 / 1000000000000) (-40318658157 / 1000000000000), orderedInterval (8583999885 / 1000000000000) (8584002764 / 1000000000000))
    | 24 => (orderedInterval (51109706244 / 1000000000000) (51109767941 / 1000000000000), orderedInterval (-37635988368 / 1000000000000) (-37635926670 / 1000000000000))
    | 25 => (orderedInterval (-27208301956 / 1000000000000) (-27208301954 / 1000000000000), orderedInterval (-15720770095 / 1000000000000) (-15720770094 / 1000000000000))
    | _ => (orderedInterval (-25966939004 / 1000000000000) (-25966939003 / 1000000000000), orderedInterval (-28342539541 / 1000000000000) (-28342539540 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14192898141 / 1000000000000) (14192899463 / 1000000000000)
      | 1 => orderedInterval (779656462 / 1000000000000) (779656509 / 1000000000000)
      | 2 => orderedInterval (-926750624 / 1000000000000) (-926750581 / 1000000000000)
      | 3 => orderedInterval (1562998939 / 1000000000000) (1563002049 / 1000000000000)
      | 4 => orderedInterval (2151889097 / 1000000000000) (2151891001 / 1000000000000)
      | 5 => orderedInterval (-223596171 / 1000000000000) (-223596126 / 1000000000000)
      | 6 => orderedInterval (2815840385 / 1000000000000) (2815840491 / 1000000000000)
      | 7 => orderedInterval (2653088262 / 1000000000000) (2653088876 / 1000000000000)
      | _ => orderedInterval (7394996735 / 1000000000000) (7394997204 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1450463447 / 1000000000000) (-1450461959 / 1000000000000)
      | 1 => orderedInterval (4347033518 / 1000000000000) (4347033568 / 1000000000000)
      | 2 => orderedInterval (-1375918916 / 1000000000000) (-1375918837 / 1000000000000)
      | 3 => orderedInterval (48887512 / 1000000000000) (48891637 / 1000000000000)
      | 4 => orderedInterval (-3684714200 / 1000000000000) (-3684711287 / 1000000000000)
      | 5 => orderedInterval (4056954824 / 1000000000000) (4056954888 / 1000000000000)
      | 6 => orderedInterval (5667952020 / 1000000000000) (5667952117 / 1000000000000)
      | 7 => orderedInterval (-1155418056 / 1000000000000) (-1155417501 / 1000000000000)
      | _ => orderedInterval (8880451614 / 1000000000000) (8880451920 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13494467073 / 1000000000000) (-13494465382 / 1000000000000)
      | 1 => orderedInterval (-2570867543 / 1000000000000) (-2570867475 / 1000000000000)
      | 2 => orderedInterval (3651692525 / 1000000000000) (3651692674 / 1000000000000)
      | 3 => orderedInterval (382426551 / 1000000000000) (382432134 / 1000000000000)
      | 4 => orderedInterval (-4073903944 / 1000000000000) (-4073899478 / 1000000000000)
      | 5 => orderedInterval (-213352627 / 1000000000000) (-213352532 / 1000000000000)
      | 6 => orderedInterval (-2278339543 / 1000000000000) (-2278339452 / 1000000000000)
      | 7 => orderedInterval (-4116148771 / 1000000000000) (-4116148253 / 1000000000000)
      | _ => orderedInterval (-15263169688 / 1000000000000) (-15263169410 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (1094006784 / 1000000000000) (1094008713 / 1000000000000)
      | 1 => orderedInterval (-8726925072 / 1000000000000) (-8726924972 / 1000000000000)
      | 2 => orderedInterval (3136576336 / 1000000000000) (3136576619 / 1000000000000)
      | 3 => orderedInterval (-3134657199 / 1000000000000) (-3134649427 / 1000000000000)
      | 4 => orderedInterval (9788936235 / 1000000000000) (9788943076 / 1000000000000)
      | 5 => orderedInterval (-8895379109 / 1000000000000) (-8895378965 / 1000000000000)
      | 6 => orderedInterval (-5804390660 / 1000000000000) (-5804390573 / 1000000000000)
      | 7 => orderedInterval (1076104018 / 1000000000000) (1076104513 / 1000000000000)
      | _ => orderedInterval (-18349376695 / 1000000000000) (-18349376351 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12321049279 / 1000000000000) (12321051496 / 1000000000000)
      | 1 => orderedInterval (6647536982 / 1000000000000) (6647537134 / 1000000000000)
      | 2 => orderedInterval (-14340064930 / 1000000000000) (-14340064384 / 1000000000000)
      | 3 => orderedInterval (-14694548658 / 1000000000000) (-14694537338 / 1000000000000)
      | 4 => orderedInterval (5047504859 / 1000000000000) (5047515367 / 1000000000000)
      | 5 => orderedInterval (2563969719 / 1000000000000) (2563969943 / 1000000000000)
      | 6 => orderedInterval (2072488137 / 1000000000000) (2072488221 / 1000000000000)
      | 7 => orderedInterval (4607873666 / 1000000000000) (4607874150 / 1000000000000)
      | _ => orderedInterval (38187886523 / 1000000000000) (38187887035 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (30401021226 / 1000000000000) (30401028886 / 1000000000000)
    | 1 => orderedInterval (15334764869 / 1000000000000) (15334774546 / 1000000000000)
    | 2 => orderedInterval (-37976130113 / 1000000000000) (-37976117174 / 1000000000000)
    | 3 => orderedInterval (-29815105362 / 1000000000000) (-29815087367 / 1000000000000)
    | _ => orderedInterval (42413695577 / 1000000000000) (42413721624 / 1000000000000)

theorem compactCertificate475_stateChecks0 :
    compactCertificate475.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (693 / 2)) (orderedInterval (42449847908 / 1000000000000) (42449849017 / 1000000000000), orderedInterval (-6002217226 / 1000000000000) (-6002216116 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1020921326895393 / 4000000000000)) (orderedInterval (-49927807555 / 1000000000000) (-49927807483 / 1000000000000), orderedInterval (-1128723473 / 1000000000000) (-1128723401 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (330144980965569 / 800000000000)) (orderedInterval (-36936998988 / 1000000000000) (-36936984390 / 1000000000000), orderedInterval (13397672652 / 1000000000000) (13397687250 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_stateChecks1 :
    compactCertificate475.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (297902296974051 / 4000000000000)) (orderedInterval (-12803385032 / 1000000000000) (-12803384966 / 1000000000000), orderedInterval (91651737890 / 1000000000000) (91651737956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (800207473096647 / 4000000000000)) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2172718951979499 / 4000000000000)) (orderedInterval (-15485465635 / 1000000000000) (-15485465634 / 1000000000000), orderedInterval (-30518102170 / 1000000000000) (-30518102169 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_stateChecks2 :
    compactCertificate475.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1600414946193987 / 4000000000000)) (orderedInterval (-37661662840 / 1000000000000) (-37661650531 / 1000000000000), orderedInterval (13189942950 / 1000000000000) (13189955258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2742338288502351 / 4000000000000)) (orderedInterval (30401743424 / 1000000000000) (30401744149 / 1000000000000), orderedInterval (2054656731 / 1000000000000) (2054657456 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2019993971350509 / 4000000000000)) (orderedInterval (453525364 / 1000000000000) (453525365 / 1000000000000), orderedInterval (-35503011020 / 1000000000000) (-35503011019 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_stateChecks3 :
    compactCertificate475.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (3099190216814307 / 4000000000000)) (orderedInterval (10913706035 / 1000000000000) (10913706049 / 1000000000000), orderedInterval (-26512714860 / 1000000000000) (-26512714846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1789318305947403 / 4000000000000)) (orderedInterval (34167684186 / 1000000000000) (34167724263 / 1000000000000), orderedInterval (-16029563620 / 1000000000000) (-16029523543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (3175176733440327 / 4000000000000)) (orderedInterval (6828338626 / 1000000000000) (6828338627 / 1000000000000), orderedInterval (-27488295471 / 1000000000000) (-27488295469 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_stateChecks4 :
    compactCertificate475.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2966661977472963 / 4000000000000)) (orderedInterval (25190003320 / 1000000000000) (25190003322 / 1000000000000), orderedInterval (14943924818 / 1000000000000) (14943924820 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2117149971068979 / 4000000000000)) (orderedInterval (26203608772 / 1000000000000) (26203628471 / 1000000000000), orderedInterval (-22743844117 / 1000000000000) (-22743824417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2400622419289941 / 4000000000000)) (orderedInterval (-25443362373 / 1000000000000) (-25443362372 / 1000000000000), orderedInterval (-20310873080 / 1000000000000) (-20310873079 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_stateChecks5 :
    compactCertificate475.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (2001388695735429 / 4000000000000)) (orderedInterval (-35628503480 / 1000000000000) (-35628502527 / 1000000000000), orderedInterval (1757586830 / 1000000000000) (1757587783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1768287608712009 / 4000000000000)) (orderedInterval (4073357491 / 1000000000000) (4073357494 / 1000000000000), orderedInterval (-37733781782 / 1000000000000) (-37733781779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (512518671324891 / 800000000000)) (orderedInterval (16440227406 / 1000000000000) (16440227407 / 1000000000000), orderedInterval (26883837931 / 1000000000000) (26883837932 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_stateChecks6 :
    compactCertificate475.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1417653617264577 / 4000000000000)) (orderedInterval (-8356918500 / 1000000000000) (-8356918499 / 1000000000000), orderedInterval (-41538502756 / 1000000000000) (-41538502755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1201760671439097 / 4000000000000)) (orderedInterval (-16549087224 / 1000000000000) (-16549086902 / 1000000000000), orderedInterval (42982014872 / 1000000000000) (42982015194 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (752006028649491 / 4000000000000)) (orderedInterval (16677936171 / 1000000000000) (16677936172 / 1000000000000), orderedInterval (55706022849 / 1000000000000) (55706022850 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_stateChecks7 :
    compactCertificate475.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (404431343266797 / 4000000000000)) (orderedInterval (77610317695 / 1000000000000) (77610317697 / 1000000000000), orderedInterval (16139276957 / 1000000000000) (16139276958 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1098109770071391 / 4000000000000)) (orderedInterval (-43910692915 / 1000000000000) (-43910677413 / 1000000000000), orderedInterval (19849009109 / 1000000000000) (19849024611 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1499375010740607 / 4000000000000)) (orderedInterval (-40318661036 / 1000000000000) (-40318658157 / 1000000000000), orderedInterval (8583999885 / 1000000000000) (8584002764 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_stateChecks8 :
    compactCertificate475.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (633993971350509 / 4000000000000)) (orderedInterval (51109706244 / 1000000000000) (51109767941 / 1000000000000), orderedInterval (-37635988368 / 1000000000000) (-37635926670 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2577150295246989 / 4000000000000)) (orderedInterval (-27208301956 / 1000000000000) (-27208301954 / 1000000000000), orderedInterval (-15720770095 / 1000000000000) (-15720770094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1721416961607651 / 4000000000000)) (orderedInterval (-25966939004 / 1000000000000) (-25966939003 / 1000000000000), orderedInterval (-28342539541 / 1000000000000) (-28342539540 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_states : ∀ j,
    BesselStateValid (compactCertificate475.point j) (compactCertificate475.state j) :=
  compactCertificate475.statesValid_of_checks3 compactCertificate475_stateChecks0
    compactCertificate475_stateChecks1 compactCertificate475_stateChecks2
    compactCertificate475_stateChecks3 compactCertificate475_stateChecks4
    compactCertificate475_stateChecks5 compactCertificate475_stateChecks6
    compactCertificate475_stateChecks7 compactCertificate475_stateChecks8

theorem compactCertificate475_chunkChecks0_0 :
    compactCertificate475.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (693 / 2) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42449847908 / 1000000000000) (42449849017 / 1000000000000), orderedInterval (-6002217226 / 1000000000000) (-6002216116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1020921326895393 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49927807555 / 1000000000000) (-49927807483 / 1000000000000), orderedInterval (-1128723473 / 1000000000000) (-1128723401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (330144980965569 / 800000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36936998988 / 1000000000000) (-36936984390 / 1000000000000), orderedInterval (13397672652 / 1000000000000) (13397687250 / 1000000000000)))) (orderedInterval (14192898141 / 1000000000000) (14192899463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (297902296974051 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12803385032 / 1000000000000) (-12803384966 / 1000000000000), orderedInterval (91651737890 / 1000000000000) (91651737956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2172718951979499 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15485465635 / 1000000000000) (-15485465634 / 1000000000000), orderedInterval (-30518102170 / 1000000000000) (-30518102169 / 1000000000000)))) (orderedInterval (779656462 / 1000000000000) (779656509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1600414946193987 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37661662840 / 1000000000000) (-37661650531 / 1000000000000), orderedInterval (13189942950 / 1000000000000) (13189955258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2742338288502351 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30401743424 / 1000000000000) (30401744149 / 1000000000000), orderedInterval (2054656731 / 1000000000000) (2054657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2019993971350509 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (453525364 / 1000000000000) (453525365 / 1000000000000), orderedInterval (-35503011020 / 1000000000000) (-35503011019 / 1000000000000)))) (orderedInterval (-926750624 / 1000000000000) (-926750581 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks0_1 :
    compactCertificate475.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3099190216814307 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10913706035 / 1000000000000) (10913706049 / 1000000000000), orderedInterval (-26512714860 / 1000000000000) (-26512714846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1789318305947403 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34167684186 / 1000000000000) (34167724263 / 1000000000000), orderedInterval (-16029563620 / 1000000000000) (-16029523543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3175176733440327 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6828338626 / 1000000000000) (6828338627 / 1000000000000), orderedInterval (-27488295471 / 1000000000000) (-27488295469 / 1000000000000)))) (orderedInterval (1562998939 / 1000000000000) (1563002049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2966661977472963 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25190003320 / 1000000000000) (25190003322 / 1000000000000), orderedInterval (14943924818 / 1000000000000) (14943924820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2117149971068979 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26203608772 / 1000000000000) (26203628471 / 1000000000000), orderedInterval (-22743844117 / 1000000000000) (-22743824417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2400622419289941 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25443362373 / 1000000000000) (-25443362372 / 1000000000000), orderedInterval (-20310873080 / 1000000000000) (-20310873079 / 1000000000000)))) (orderedInterval (2151889097 / 1000000000000) (2151891001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2001388695735429 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35628503480 / 1000000000000) (-35628502527 / 1000000000000), orderedInterval (1757586830 / 1000000000000) (1757587783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1768287608712009 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4073357491 / 1000000000000) (4073357494 / 1000000000000), orderedInterval (-37733781782 / 1000000000000) (-37733781779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (512518671324891 / 800000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16440227406 / 1000000000000) (16440227407 / 1000000000000), orderedInterval (26883837931 / 1000000000000) (26883837932 / 1000000000000)))) (orderedInterval (-223596171 / 1000000000000) (-223596126 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks0_2 :
    compactCertificate475.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1417653617264577 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8356918500 / 1000000000000) (-8356918499 / 1000000000000), orderedInterval (-41538502756 / 1000000000000) (-41538502755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1201760671439097 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16549087224 / 1000000000000) (-16549086902 / 1000000000000), orderedInterval (42982014872 / 1000000000000) (42982015194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (752006028649491 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16677936171 / 1000000000000) (16677936172 / 1000000000000), orderedInterval (55706022849 / 1000000000000) (55706022850 / 1000000000000)))) (orderedInterval (2815840385 / 1000000000000) (2815840491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (404431343266797 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77610317695 / 1000000000000) (77610317697 / 1000000000000), orderedInterval (16139276957 / 1000000000000) (16139276958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1098109770071391 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43910692915 / 1000000000000) (-43910677413 / 1000000000000), orderedInterval (19849009109 / 1000000000000) (19849024611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1499375010740607 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40318661036 / 1000000000000) (-40318658157 / 1000000000000), orderedInterval (8583999885 / 1000000000000) (8584002764 / 1000000000000)))) (orderedInterval (2653088262 / 1000000000000) (2653088876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (633993971350509 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51109706244 / 1000000000000) (51109767941 / 1000000000000), orderedInterval (-37635988368 / 1000000000000) (-37635926670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2577150295246989 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27208301956 / 1000000000000) (-27208301954 / 1000000000000), orderedInterval (-15720770095 / 1000000000000) (-15720770094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1721416961607651 / 4000000000000) 0 (IntervalRat.scale (693 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25966939004 / 1000000000000) (-25966939003 / 1000000000000), orderedInterval (-28342539541 / 1000000000000) (-28342539540 / 1000000000000)))) (orderedInterval (7394996735 / 1000000000000) (7394997204 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks0 :
    compactCertificate475.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate475.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate475_chunkChecks0_0
    compactCertificate475_chunkChecks0_1 compactCertificate475_chunkChecks0_2

theorem compactCertificate475_chunkChecks1_0 :
    compactCertificate475.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (693 / 2) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42449847908 / 1000000000000) (42449849017 / 1000000000000), orderedInterval (-6002217226 / 1000000000000) (-6002216116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1020921326895393 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49927807555 / 1000000000000) (-49927807483 / 1000000000000), orderedInterval (-1128723473 / 1000000000000) (-1128723401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (330144980965569 / 800000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36936998988 / 1000000000000) (-36936984390 / 1000000000000), orderedInterval (13397672652 / 1000000000000) (13397687250 / 1000000000000)))) (orderedInterval (-1450463447 / 1000000000000) (-1450461959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (297902296974051 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12803385032 / 1000000000000) (-12803384966 / 1000000000000), orderedInterval (91651737890 / 1000000000000) (91651737956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2172718951979499 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15485465635 / 1000000000000) (-15485465634 / 1000000000000), orderedInterval (-30518102170 / 1000000000000) (-30518102169 / 1000000000000)))) (orderedInterval (4347033518 / 1000000000000) (4347033568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1600414946193987 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37661662840 / 1000000000000) (-37661650531 / 1000000000000), orderedInterval (13189942950 / 1000000000000) (13189955258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2742338288502351 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30401743424 / 1000000000000) (30401744149 / 1000000000000), orderedInterval (2054656731 / 1000000000000) (2054657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2019993971350509 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (453525364 / 1000000000000) (453525365 / 1000000000000), orderedInterval (-35503011020 / 1000000000000) (-35503011019 / 1000000000000)))) (orderedInterval (-1375918916 / 1000000000000) (-1375918837 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks1_1 :
    compactCertificate475.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3099190216814307 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10913706035 / 1000000000000) (10913706049 / 1000000000000), orderedInterval (-26512714860 / 1000000000000) (-26512714846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1789318305947403 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34167684186 / 1000000000000) (34167724263 / 1000000000000), orderedInterval (-16029563620 / 1000000000000) (-16029523543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3175176733440327 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6828338626 / 1000000000000) (6828338627 / 1000000000000), orderedInterval (-27488295471 / 1000000000000) (-27488295469 / 1000000000000)))) (orderedInterval (48887512 / 1000000000000) (48891637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2966661977472963 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25190003320 / 1000000000000) (25190003322 / 1000000000000), orderedInterval (14943924818 / 1000000000000) (14943924820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2117149971068979 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26203608772 / 1000000000000) (26203628471 / 1000000000000), orderedInterval (-22743844117 / 1000000000000) (-22743824417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2400622419289941 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25443362373 / 1000000000000) (-25443362372 / 1000000000000), orderedInterval (-20310873080 / 1000000000000) (-20310873079 / 1000000000000)))) (orderedInterval (-3684714200 / 1000000000000) (-3684711287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2001388695735429 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35628503480 / 1000000000000) (-35628502527 / 1000000000000), orderedInterval (1757586830 / 1000000000000) (1757587783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1768287608712009 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4073357491 / 1000000000000) (4073357494 / 1000000000000), orderedInterval (-37733781782 / 1000000000000) (-37733781779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (512518671324891 / 800000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16440227406 / 1000000000000) (16440227407 / 1000000000000), orderedInterval (26883837931 / 1000000000000) (26883837932 / 1000000000000)))) (orderedInterval (4056954824 / 1000000000000) (4056954888 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks1_2 :
    compactCertificate475.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1417653617264577 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8356918500 / 1000000000000) (-8356918499 / 1000000000000), orderedInterval (-41538502756 / 1000000000000) (-41538502755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1201760671439097 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16549087224 / 1000000000000) (-16549086902 / 1000000000000), orderedInterval (42982014872 / 1000000000000) (42982015194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (752006028649491 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16677936171 / 1000000000000) (16677936172 / 1000000000000), orderedInterval (55706022849 / 1000000000000) (55706022850 / 1000000000000)))) (orderedInterval (5667952020 / 1000000000000) (5667952117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (404431343266797 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77610317695 / 1000000000000) (77610317697 / 1000000000000), orderedInterval (16139276957 / 1000000000000) (16139276958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1098109770071391 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43910692915 / 1000000000000) (-43910677413 / 1000000000000), orderedInterval (19849009109 / 1000000000000) (19849024611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1499375010740607 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40318661036 / 1000000000000) (-40318658157 / 1000000000000), orderedInterval (8583999885 / 1000000000000) (8584002764 / 1000000000000)))) (orderedInterval (-1155418056 / 1000000000000) (-1155417501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (633993971350509 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51109706244 / 1000000000000) (51109767941 / 1000000000000), orderedInterval (-37635988368 / 1000000000000) (-37635926670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2577150295246989 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27208301956 / 1000000000000) (-27208301954 / 1000000000000), orderedInterval (-15720770095 / 1000000000000) (-15720770094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1721416961607651 / 4000000000000) 1 (IntervalRat.scale (693 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25966939004 / 1000000000000) (-25966939003 / 1000000000000), orderedInterval (-28342539541 / 1000000000000) (-28342539540 / 1000000000000)))) (orderedInterval (8880451614 / 1000000000000) (8880451920 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks1 :
    compactCertificate475.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate475.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate475_chunkChecks1_0
    compactCertificate475_chunkChecks1_1 compactCertificate475_chunkChecks1_2

theorem compactCertificate475_chunkChecks2_0 :
    compactCertificate475.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (693 / 2) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42449847908 / 1000000000000) (42449849017 / 1000000000000), orderedInterval (-6002217226 / 1000000000000) (-6002216116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1020921326895393 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49927807555 / 1000000000000) (-49927807483 / 1000000000000), orderedInterval (-1128723473 / 1000000000000) (-1128723401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (330144980965569 / 800000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36936998988 / 1000000000000) (-36936984390 / 1000000000000), orderedInterval (13397672652 / 1000000000000) (13397687250 / 1000000000000)))) (orderedInterval (-13494467073 / 1000000000000) (-13494465382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (297902296974051 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12803385032 / 1000000000000) (-12803384966 / 1000000000000), orderedInterval (91651737890 / 1000000000000) (91651737956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2172718951979499 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15485465635 / 1000000000000) (-15485465634 / 1000000000000), orderedInterval (-30518102170 / 1000000000000) (-30518102169 / 1000000000000)))) (orderedInterval (-2570867543 / 1000000000000) (-2570867475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1600414946193987 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37661662840 / 1000000000000) (-37661650531 / 1000000000000), orderedInterval (13189942950 / 1000000000000) (13189955258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2742338288502351 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30401743424 / 1000000000000) (30401744149 / 1000000000000), orderedInterval (2054656731 / 1000000000000) (2054657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2019993971350509 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (453525364 / 1000000000000) (453525365 / 1000000000000), orderedInterval (-35503011020 / 1000000000000) (-35503011019 / 1000000000000)))) (orderedInterval (3651692525 / 1000000000000) (3651692674 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks2_1 :
    compactCertificate475.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3099190216814307 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10913706035 / 1000000000000) (10913706049 / 1000000000000), orderedInterval (-26512714860 / 1000000000000) (-26512714846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1789318305947403 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34167684186 / 1000000000000) (34167724263 / 1000000000000), orderedInterval (-16029563620 / 1000000000000) (-16029523543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3175176733440327 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6828338626 / 1000000000000) (6828338627 / 1000000000000), orderedInterval (-27488295471 / 1000000000000) (-27488295469 / 1000000000000)))) (orderedInterval (382426551 / 1000000000000) (382432134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2966661977472963 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25190003320 / 1000000000000) (25190003322 / 1000000000000), orderedInterval (14943924818 / 1000000000000) (14943924820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2117149971068979 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26203608772 / 1000000000000) (26203628471 / 1000000000000), orderedInterval (-22743844117 / 1000000000000) (-22743824417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2400622419289941 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25443362373 / 1000000000000) (-25443362372 / 1000000000000), orderedInterval (-20310873080 / 1000000000000) (-20310873079 / 1000000000000)))) (orderedInterval (-4073903944 / 1000000000000) (-4073899478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2001388695735429 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35628503480 / 1000000000000) (-35628502527 / 1000000000000), orderedInterval (1757586830 / 1000000000000) (1757587783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1768287608712009 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4073357491 / 1000000000000) (4073357494 / 1000000000000), orderedInterval (-37733781782 / 1000000000000) (-37733781779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (512518671324891 / 800000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16440227406 / 1000000000000) (16440227407 / 1000000000000), orderedInterval (26883837931 / 1000000000000) (26883837932 / 1000000000000)))) (orderedInterval (-213352627 / 1000000000000) (-213352532 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks2_2 :
    compactCertificate475.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1417653617264577 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8356918500 / 1000000000000) (-8356918499 / 1000000000000), orderedInterval (-41538502756 / 1000000000000) (-41538502755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1201760671439097 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16549087224 / 1000000000000) (-16549086902 / 1000000000000), orderedInterval (42982014872 / 1000000000000) (42982015194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (752006028649491 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16677936171 / 1000000000000) (16677936172 / 1000000000000), orderedInterval (55706022849 / 1000000000000) (55706022850 / 1000000000000)))) (orderedInterval (-2278339543 / 1000000000000) (-2278339452 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (404431343266797 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77610317695 / 1000000000000) (77610317697 / 1000000000000), orderedInterval (16139276957 / 1000000000000) (16139276958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1098109770071391 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43910692915 / 1000000000000) (-43910677413 / 1000000000000), orderedInterval (19849009109 / 1000000000000) (19849024611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1499375010740607 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40318661036 / 1000000000000) (-40318658157 / 1000000000000), orderedInterval (8583999885 / 1000000000000) (8584002764 / 1000000000000)))) (orderedInterval (-4116148771 / 1000000000000) (-4116148253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (633993971350509 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51109706244 / 1000000000000) (51109767941 / 1000000000000), orderedInterval (-37635988368 / 1000000000000) (-37635926670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2577150295246989 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27208301956 / 1000000000000) (-27208301954 / 1000000000000), orderedInterval (-15720770095 / 1000000000000) (-15720770094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1721416961607651 / 4000000000000) 2 (IntervalRat.scale (693 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25966939004 / 1000000000000) (-25966939003 / 1000000000000), orderedInterval (-28342539541 / 1000000000000) (-28342539540 / 1000000000000)))) (orderedInterval (-15263169688 / 1000000000000) (-15263169410 / 1000000000000))) = true
  rfl'

theorem compactCertificate475_chunkChecks2 :
    compactCertificate475.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate475.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate475_chunkChecks2_0
    compactCertificate475_chunkChecks2_1 compactCertificate475_chunkChecks2_2

theorem compactCertificate475_chunkChecks3_0 :
    compactCertificate475.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (693 / 2) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42449847908 / 1000000000000) (42449849017 / 1000000000000), orderedInterval (-6002217226 / 1000000000000) (-6002216116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1020921326895393 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49927807555 / 1000000000000) (-49927807483 / 1000000000000), orderedInterval (-1128723473 / 1000000000000) (-1128723401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (330144980965569 / 800000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36936998988 / 1000000000000) (-36936984390 / 1000000000000), orderedInterval (13397672652 / 1000000000000) (13397687250 / 1000000000000)))) (orderedInterval (1094006784 / 1000000000000) (1094008713 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (297902296974051 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12803385032 / 1000000000000) (-12803384966 / 1000000000000), orderedInterval (91651737890 / 1000000000000) (91651737956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2172718951979499 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15485465635 / 1000000000000) (-15485465634 / 1000000000000), orderedInterval (-30518102170 / 1000000000000) (-30518102169 / 1000000000000)))) (orderedInterval (-8726925072 / 1000000000000) (-8726924972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1600414946193987 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37661662840 / 1000000000000) (-37661650531 / 1000000000000), orderedInterval (13189942950 / 1000000000000) (13189955258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2742338288502351 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30401743424 / 1000000000000) (30401744149 / 1000000000000), orderedInterval (2054656731 / 1000000000000) (2054657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2019993971350509 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (453525364 / 1000000000000) (453525365 / 1000000000000), orderedInterval (-35503011020 / 1000000000000) (-35503011019 / 1000000000000)))) (orderedInterval (3136576336 / 1000000000000) (3136576619 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate475_chunkChecks3_1 :
    compactCertificate475.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3099190216814307 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10913706035 / 1000000000000) (10913706049 / 1000000000000), orderedInterval (-26512714860 / 1000000000000) (-26512714846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1789318305947403 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34167684186 / 1000000000000) (34167724263 / 1000000000000), orderedInterval (-16029563620 / 1000000000000) (-16029523543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3175176733440327 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6828338626 / 1000000000000) (6828338627 / 1000000000000), orderedInterval (-27488295471 / 1000000000000) (-27488295469 / 1000000000000)))) (orderedInterval (-3134657199 / 1000000000000) (-3134649427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2966661977472963 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25190003320 / 1000000000000) (25190003322 / 1000000000000), orderedInterval (14943924818 / 1000000000000) (14943924820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2117149971068979 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26203608772 / 1000000000000) (26203628471 / 1000000000000), orderedInterval (-22743844117 / 1000000000000) (-22743824417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2400622419289941 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25443362373 / 1000000000000) (-25443362372 / 1000000000000), orderedInterval (-20310873080 / 1000000000000) (-20310873079 / 1000000000000)))) (orderedInterval (9788936235 / 1000000000000) (9788943076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2001388695735429 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35628503480 / 1000000000000) (-35628502527 / 1000000000000), orderedInterval (1757586830 / 1000000000000) (1757587783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1768287608712009 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4073357491 / 1000000000000) (4073357494 / 1000000000000), orderedInterval (-37733781782 / 1000000000000) (-37733781779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (512518671324891 / 800000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16440227406 / 1000000000000) (16440227407 / 1000000000000), orderedInterval (26883837931 / 1000000000000) (26883837932 / 1000000000000)))) (orderedInterval (-8895379109 / 1000000000000) (-8895378965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate475_chunkChecks3_2 :
    compactCertificate475.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1417653617264577 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8356918500 / 1000000000000) (-8356918499 / 1000000000000), orderedInterval (-41538502756 / 1000000000000) (-41538502755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1201760671439097 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16549087224 / 1000000000000) (-16549086902 / 1000000000000), orderedInterval (42982014872 / 1000000000000) (42982015194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (752006028649491 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16677936171 / 1000000000000) (16677936172 / 1000000000000), orderedInterval (55706022849 / 1000000000000) (55706022850 / 1000000000000)))) (orderedInterval (-5804390660 / 1000000000000) (-5804390573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (404431343266797 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77610317695 / 1000000000000) (77610317697 / 1000000000000), orderedInterval (16139276957 / 1000000000000) (16139276958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1098109770071391 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43910692915 / 1000000000000) (-43910677413 / 1000000000000), orderedInterval (19849009109 / 1000000000000) (19849024611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1499375010740607 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40318661036 / 1000000000000) (-40318658157 / 1000000000000), orderedInterval (8583999885 / 1000000000000) (8584002764 / 1000000000000)))) (orderedInterval (1076104018 / 1000000000000) (1076104513 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (633993971350509 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51109706244 / 1000000000000) (51109767941 / 1000000000000), orderedInterval (-37635988368 / 1000000000000) (-37635926670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2577150295246989 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27208301956 / 1000000000000) (-27208301954 / 1000000000000), orderedInterval (-15720770095 / 1000000000000) (-15720770094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1721416961607651 / 4000000000000) 3 (IntervalRat.scale (693 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25966939004 / 1000000000000) (-25966939003 / 1000000000000), orderedInterval (-28342539541 / 1000000000000) (-28342539540 / 1000000000000)))) (orderedInterval (-18349376695 / 1000000000000) (-18349376351 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate475_chunkChecks3 :
    compactCertificate475.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate475.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate475_chunkChecks3_0
    compactCertificate475_chunkChecks3_1 compactCertificate475_chunkChecks3_2

theorem compactCertificate475_chunkChecks4_0 :
    compactCertificate475.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (693 / 2) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42449847908 / 1000000000000) (42449849017 / 1000000000000), orderedInterval (-6002217226 / 1000000000000) (-6002216116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1020921326895393 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49927807555 / 1000000000000) (-49927807483 / 1000000000000), orderedInterval (-1128723473 / 1000000000000) (-1128723401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (330144980965569 / 800000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36936998988 / 1000000000000) (-36936984390 / 1000000000000), orderedInterval (13397672652 / 1000000000000) (13397687250 / 1000000000000)))) (orderedInterval (12321049279 / 1000000000000) (12321051496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (297902296974051 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12803385032 / 1000000000000) (-12803384966 / 1000000000000), orderedInterval (91651737890 / 1000000000000) (91651737956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (800207473096647 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12601625746 / 1000000000000) (-12601625653 / 1000000000000), orderedInterval (55017689768 / 1000000000000) (55017689861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2172718951979499 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15485465635 / 1000000000000) (-15485465634 / 1000000000000), orderedInterval (-30518102170 / 1000000000000) (-30518102169 / 1000000000000)))) (orderedInterval (6647536982 / 1000000000000) (6647537134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1600414946193987 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37661662840 / 1000000000000) (-37661650531 / 1000000000000), orderedInterval (13189942950 / 1000000000000) (13189955258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2742338288502351 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30401743424 / 1000000000000) (30401744149 / 1000000000000), orderedInterval (2054656731 / 1000000000000) (2054657456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2019993971350509 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (453525364 / 1000000000000) (453525365 / 1000000000000), orderedInterval (-35503011020 / 1000000000000) (-35503011019 / 1000000000000)))) (orderedInterval (-14340064930 / 1000000000000) (-14340064384 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate475_chunkChecks4_1 :
    compactCertificate475.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3099190216814307 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10913706035 / 1000000000000) (10913706049 / 1000000000000), orderedInterval (-26512714860 / 1000000000000) (-26512714846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1789318305947403 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34167684186 / 1000000000000) (34167724263 / 1000000000000), orderedInterval (-16029563620 / 1000000000000) (-16029523543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3175176733440327 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6828338626 / 1000000000000) (6828338627 / 1000000000000), orderedInterval (-27488295471 / 1000000000000) (-27488295469 / 1000000000000)))) (orderedInterval (-14694548658 / 1000000000000) (-14694537338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2966661977472963 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25190003320 / 1000000000000) (25190003322 / 1000000000000), orderedInterval (14943924818 / 1000000000000) (14943924820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2117149971068979 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26203608772 / 1000000000000) (26203628471 / 1000000000000), orderedInterval (-22743844117 / 1000000000000) (-22743824417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2400622419289941 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25443362373 / 1000000000000) (-25443362372 / 1000000000000), orderedInterval (-20310873080 / 1000000000000) (-20310873079 / 1000000000000)))) (orderedInterval (5047504859 / 1000000000000) (5047515367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2001388695735429 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35628503480 / 1000000000000) (-35628502527 / 1000000000000), orderedInterval (1757586830 / 1000000000000) (1757587783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1768287608712009 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4073357491 / 1000000000000) (4073357494 / 1000000000000), orderedInterval (-37733781782 / 1000000000000) (-37733781779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (512518671324891 / 800000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16440227406 / 1000000000000) (16440227407 / 1000000000000), orderedInterval (26883837931 / 1000000000000) (26883837932 / 1000000000000)))) (orderedInterval (2563969719 / 1000000000000) (2563969943 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate475_chunkChecks4_2 :
    compactCertificate475.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1417653617264577 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8356918500 / 1000000000000) (-8356918499 / 1000000000000), orderedInterval (-41538502756 / 1000000000000) (-41538502755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1201760671439097 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16549087224 / 1000000000000) (-16549086902 / 1000000000000), orderedInterval (42982014872 / 1000000000000) (42982015194 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (752006028649491 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16677936171 / 1000000000000) (16677936172 / 1000000000000), orderedInterval (55706022849 / 1000000000000) (55706022850 / 1000000000000)))) (orderedInterval (2072488137 / 1000000000000) (2072488221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (404431343266797 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77610317695 / 1000000000000) (77610317697 / 1000000000000), orderedInterval (16139276957 / 1000000000000) (16139276958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1098109770071391 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43910692915 / 1000000000000) (-43910677413 / 1000000000000), orderedInterval (19849009109 / 1000000000000) (19849024611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1499375010740607 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40318661036 / 1000000000000) (-40318658157 / 1000000000000), orderedInterval (8583999885 / 1000000000000) (8584002764 / 1000000000000)))) (orderedInterval (4607873666 / 1000000000000) (4607874150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (633993971350509 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51109706244 / 1000000000000) (51109767941 / 1000000000000), orderedInterval (-37635988368 / 1000000000000) (-37635926670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2577150295246989 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27208301956 / 1000000000000) (-27208301954 / 1000000000000), orderedInterval (-15720770095 / 1000000000000) (-15720770094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1721416961607651 / 4000000000000) 4 (IntervalRat.scale (693 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25966939004 / 1000000000000) (-25966939003 / 1000000000000), orderedInterval (-28342539541 / 1000000000000) (-28342539540 / 1000000000000)))) (orderedInterval (38187886523 / 1000000000000) (38187887035 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate475_chunkChecks4 :
    compactCertificate475.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate475.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate475_chunkChecks4_0
    compactCertificate475_chunkChecks4_1 compactCertificate475_chunkChecks4_2

theorem compactCertificate475_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate475.chunkCheck r b = true :=
  compactCertificate475.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate475_chunkChecks0
    · exact compactCertificate475_chunkChecks1
    · exact compactCertificate475_chunkChecks2
    · exact compactCertificate475_chunkChecks3
    · exact compactCertificate475_chunkChecks4)

theorem compactCertificate475_coefficient0 :
    compactCertificate475.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate475_coefficient1 :
    compactCertificate475.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate475_coefficient2 :
    compactCertificate475.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate475_coefficient3 :
    compactCertificate475.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate475_coefficient4 :
    compactCertificate475.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate475_coefficients : ∀ r : Fin 5,
    compactCertificate475.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate475_coefficient0
  · exact compactCertificate475_coefficient1
  · exact compactCertificate475_coefficient2
  · exact compactCertificate475_coefficient3
  · exact compactCertificate475_coefficient4

theorem compactCertificate475_lower : (1 : ℚ) ≤ compactCertificate475.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate475, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate475_proves {t : ℝ} (ht : t ∈ compactCertificate475.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate475.proves compactCertificate475_states compactCertificate475_chunks
    compactCertificate475_coefficients compactCertificate475_lower ht

end Erdos232
