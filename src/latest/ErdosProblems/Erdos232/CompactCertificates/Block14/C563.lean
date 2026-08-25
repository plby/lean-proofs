/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate563 : CompactCertificate where
  left := 434
  right := 435
  center := 869 / 2
  grid := fun i =>
    match i.val with
    | 0 => 138
    | 1 => 102
    | 2 => 165
    | 3 => 30
    | 4 => 80
    | 5 => 217
    | 6 => 160
    | 7 => 274
    | 8 => 202
    | 9 => 309
    | 10 => 179
    | 11 => 317
    | 12 => 296
    | 13 => 211
    | 14 => 240
    | 15 => 200
    | 16 => 177
    | 17 => 256
    | 18 => 142
    | 19 => 120
    | 20 => 75
    | 21 => 40
    | 22 => 110
    | 23 => 150
    | 24 => 63
    | 25 => 257
    | _ => 172
  point := fun i =>
    match i.val with
    | 0 => 869 / 2
    | 1 => 1280202933725969 / 4000000000000
    | 2 => 413991325337777 / 800000000000
    | 3 => 373560023189683 / 4000000000000
    | 4 => 1003434767851351 / 4000000000000
    | 5 => 2724520590577467 / 4000000000000
    | 6 => 2006869535703571 / 4000000000000
    | 7 => 3438805155423583 / 4000000000000
    | 8 => 2533008313280797 / 4000000000000
    | 9 => 3886286144894131 / 4000000000000
    | 10 => 2243748351902299 / 4000000000000
    | 11 => 3981570824472791 / 4000000000000
    | 12 => 3720099940005779 / 4000000000000
    | 13 => 2654838852610307 / 4000000000000
    | 14 => 3010304303554053 / 4000000000000
    | 15 => 2509677888303157 / 4000000000000
    | 16 => 2217376525210297 / 4000000000000
    | 17 => 642682143407403 / 800000000000
    | 18 => 1777692631173041 / 4000000000000
    | 19 => 1506969730852201 / 4000000000000
    | 20 => 942991686719203 / 4000000000000
    | 21 => 507144065366301 / 4000000000000
    | 22 => 1376994791041903 / 4000000000000
    | 23 => 1880168664262031 / 4000000000000
    | 24 => 795008313280797 / 4000000000000
    | 25 => 3231664655944637 / 4000000000000
    | _ => 2158602221698483 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (37696137291 / 1000000000000) (37696140054 / 1000000000000), orderedInterval (-6690037590 / 1000000000000) (-6690034827 / 1000000000000))
    | 1 => (orderedInterval (17091865911 / 1000000000000) (17091865912 / 1000000000000), orderedInterval (41167852065 / 1000000000000) (41167852066 / 1000000000000))
    | 2 => (orderedInterval (3099138544 / 1000000000000) (3099138546 / 1000000000000), orderedInterval (-34940149655 / 1000000000000) (-34940149653 / 1000000000000))
    | 3 => (orderedInterval (-6080560071 / 1000000000000) (-6080560049 / 1000000000000), orderedInterval (82372764772 / 1000000000000) (82372764794 / 1000000000000))
    | 4 => (orderedInterval (15663850716 / 1000000000000) (15663850717 / 1000000000000), orderedInterval (47847901530 / 1000000000000) (47847901531 / 1000000000000))
    | 5 => (orderedInterval (-5766497075 / 1000000000000) (-5766497074 / 1000000000000), orderedInterval (-30019089868 / 1000000000000) (-30019089867 / 1000000000000))
    | 6 => (orderedInterval (-5403888314 / 1000000000000) (-5403888311 / 1000000000000), orderedInterval (35214472627 / 1000000000000) (35214472630 / 1000000000000))
    | 7 => (orderedInterval (-8297361025 / 1000000000000) (-8297361023 / 1000000000000), orderedInterval (25921358279 / 1000000000000) (25921358282 / 1000000000000))
    | 8 => (orderedInterval (-16961212737 / 1000000000000) (-16961212277 / 1000000000000), orderedInterval (26802111512 / 1000000000000) (26802111972 / 1000000000000))
    | 9 => (orderedInterval (-25583115926 / 1000000000000) (-25583105013 / 1000000000000), orderedInterval (880233762 / 1000000000000) (880244675 / 1000000000000))
    | 10 => (orderedInterval (19651545776 / 1000000000000) (19651547227 / 1000000000000), orderedInterval (-27380608239 / 1000000000000) (-27380606788 / 1000000000000))
    | 11 => (orderedInterval (-7306902894 / 1000000000000) (-7306902893 / 1000000000000), orderedInterval (-24207394884 / 1000000000000) (-24207394883 / 1000000000000))
    | 12 => (orderedInterval (20475275081 / 1000000000000) (20475275082 / 1000000000000), orderedInterval (16276474633 / 1000000000000) (16276474634 / 1000000000000))
    | 13 => (orderedInterval (-30934907955 / 1000000000000) (-30934905489 / 1000000000000), orderedInterval (1511700299 / 1000000000000) (1511702765 / 1000000000000))
    | 14 => (orderedInterval (-16921223368 / 1000000000000) (-16921222931 / 1000000000000), orderedInterval (23666961976 / 1000000000000) (23666962413 / 1000000000000))
    | 15 => (orderedInterval (-3619030850 / 1000000000000) (-3619030848 / 1000000000000), orderedInterval (31650421790 / 1000000000000) (31650421791 / 1000000000000))
    | 16 => (orderedInterval (27218044230 / 1000000000000) (27218079650 / 1000000000000), orderedInterval (-20213592268 / 1000000000000) (-20213556848 / 1000000000000))
    | 17 => (orderedInterval (-3084653370 / 1000000000000) (-3084653369 / 1000000000000), orderedInterval (27982962107 / 1000000000000) (27982962108 / 1000000000000))
    | 18 => (orderedInterval (-29597392176 / 1000000000000) (-29597349408 / 1000000000000), orderedInterval (23622649308 / 1000000000000) (23622692076 / 1000000000000))
    | 19 => (orderedInterval (21006927767 / 1000000000000) (21006927768 / 1000000000000), orderedInterval (35306392439 / 1000000000000) (35306392440 / 1000000000000))
    | 20 => (orderedInterval (-41133321149 / 1000000000000) (-41133321148 / 1000000000000), orderedInterval (-31669242581 / 1000000000000) (-31669242580 / 1000000000000))
    | 21 => (orderedInterval (66899546374 / 1000000000000) (66899549326 / 1000000000000), orderedInterval (-23622643100 / 1000000000000) (-23622640149 / 1000000000000))
    | 22 => (orderedInterval (-22163435550 / 1000000000000) (-22163433544 / 1000000000000), orderedInterval (36884394560 / 1000000000000) (36884396567 / 1000000000000))
    | 23 => (orderedInterval (-14723599770 / 1000000000000) (-14723599585 / 1000000000000), orderedInterval (33744059097 / 1000000000000) (33744059282 / 1000000000000))
    | 24 => (orderedInterval (-56536587114 / 1000000000000) (-56536586984 / 1000000000000), orderedInterval (2728555195 / 1000000000000) (2728555324 / 1000000000000))
    | 25 => (orderedInterval (-27136822151 / 1000000000000) (-27136822013 / 1000000000000), orderedInterval (-7164450238 / 1000000000000) (-7164450101 / 1000000000000))
    | _ => (orderedInterval (2805924057 / 1000000000000) (2805924058 / 1000000000000), orderedInterval (34229201158 / 1000000000000) (34229201159 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15282553193 / 1000000000000) (15282554319 / 1000000000000)
      | 1 => orderedInterval (1047822485 / 1000000000000) (1047822538 / 1000000000000)
      | 2 => orderedInterval (-153995248 / 1000000000000) (-153995212 / 1000000000000)
      | 3 => orderedInterval (4963107315 / 1000000000000) (4963109534 / 1000000000000)
      | 4 => orderedInterval (-3209304349 / 1000000000000) (-3209304061 / 1000000000000)
      | 5 => orderedInterval (-1678370958 / 1000000000000) (-1678368889 / 1000000000000)
      | 6 => orderedInterval (2204294814 / 1000000000000) (2204301762 / 1000000000000)
      | 7 => orderedInterval (395910761 / 1000000000000) (395910928 / 1000000000000)
      | _ => orderedInterval (1341698597 / 1000000000000) (1341698729 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4811074176 / 1000000000000) (-4811073046 / 1000000000000)
      | 1 => orderedInterval (4161920999 / 1000000000000) (4161921059 / 1000000000000)
      | 2 => orderedInterval (-637871908 / 1000000000000) (-637871849 / 1000000000000)
      | 3 => orderedInterval (-10852225871 / 1000000000000) (-10852221039 / 1000000000000)
      | 4 => orderedInterval (-618035022 / 1000000000000) (-618034578 / 1000000000000)
      | 5 => orderedInterval (3328277191 / 1000000000000) (3328279838 / 1000000000000)
      | 6 => orderedInterval (-6155447901 / 1000000000000) (-6155440805 / 1000000000000)
      | 7 => orderedInterval (-3333348742 / 1000000000000) (-3333348628 / 1000000000000)
      | _ => orderedInterval (-6884593871 / 1000000000000) (-6884593681 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15274735454 / 1000000000000) (-15274734316 / 1000000000000)
      | 1 => orderedInterval (-1210657785 / 1000000000000) (-1210657702 / 1000000000000)
      | 2 => orderedInterval (-129729919 / 1000000000000) (-129729819 / 1000000000000)
      | 3 => orderedInterval (-19679380959 / 1000000000000) (-19679370308 / 1000000000000)
      | 4 => orderedInterval (8263735436 / 1000000000000) (8263736127 / 1000000000000)
      | 5 => orderedInterval (2884801887 / 1000000000000) (2884805282 / 1000000000000)
      | 6 => orderedInterval (-3648747367 / 1000000000000) (-3648740101 / 1000000000000)
      | 7 => orderedInterval (-1523332888 / 1000000000000) (-1523332791 / 1000000000000)
      | _ => orderedInterval (-6738136660 / 1000000000000) (-6738136371 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (5997353914 / 1000000000000) (5997355058 / 1000000000000)
      | 1 => orderedInterval (-8545533102 / 1000000000000) (-8545532979 / 1000000000000)
      | 2 => orderedInterval (4188045925 / 1000000000000) (4188046097 / 1000000000000)
      | 3 => orderedInterval (47532881028 / 1000000000000) (47532904640 / 1000000000000)
      | 4 => orderedInterval (2975354358 / 1000000000000) (2975355438 / 1000000000000)
      | 5 => orderedInterval (-8037757944 / 1000000000000) (-8037753589 / 1000000000000)
      | 6 => orderedInterval (5517532434 / 1000000000000) (5517539861 / 1000000000000)
      | 7 => orderedInterval (3682881764 / 1000000000000) (3682881854 / 1000000000000)
      | _ => orderedInterval (8569005008 / 1000000000000) (8569005466 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15326546636 / 1000000000000) (15326547789 / 1000000000000)
      | 1 => orderedInterval (2578610827 / 1000000000000) (2578611016 / 1000000000000)
      | 2 => orderedInterval (2053569118 / 1000000000000) (2053569423 / 1000000000000)
      | 3 => orderedInterval (88860879702 / 1000000000000) (88860932305 / 1000000000000)
      | 4 => orderedInterval (-22928476829 / 1000000000000) (-22928475126 / 1000000000000)
      | 5 => orderedInterval (-5194453417 / 1000000000000) (-5194447808 / 1000000000000)
      | 6 => orderedInterval (4366233668 / 1000000000000) (4366241279 / 1000000000000)
      | 7 => orderedInterval (1717646754 / 1000000000000) (1717646842 / 1000000000000)
      | _ => orderedInterval (25098633890 / 1000000000000) (25098634643 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (20193716610 / 1000000000000) (20193729648 / 1000000000000)
    | 1 => orderedInterval (-25802399301 / 1000000000000) (-25802382729 / 1000000000000)
    | 2 => orderedInterval (-37056183709 / 1000000000000) (-37056159999 / 1000000000000)
    | 3 => orderedInterval (61879763385 / 1000000000000) (61879801846 / 1000000000000)
    | _ => orderedInterval (111879190349 / 1000000000000) (111879260363 / 1000000000000)

theorem compactCertificate563_stateChecks0 :
    compactCertificate563.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (869 / 2)) (orderedInterval (37696137291 / 1000000000000) (37696140054 / 1000000000000), orderedInterval (-6690037590 / 1000000000000) (-6690034827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1280202933725969 / 4000000000000)) (orderedInterval (17091865911 / 1000000000000) (17091865912 / 1000000000000), orderedInterval (41167852065 / 1000000000000) (41167852066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (413991325337777 / 800000000000)) (orderedInterval (3099138544 / 1000000000000) (3099138546 / 1000000000000), orderedInterval (-34940149655 / 1000000000000) (-34940149653 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_stateChecks1 :
    compactCertificate563.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (373560023189683 / 4000000000000)) (orderedInterval (-6080560071 / 1000000000000) (-6080560049 / 1000000000000), orderedInterval (82372764772 / 1000000000000) (82372764794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1003434767851351 / 4000000000000)) (orderedInterval (15663850716 / 1000000000000) (15663850717 / 1000000000000), orderedInterval (47847901530 / 1000000000000) (47847901531 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2724520590577467 / 4000000000000)) (orderedInterval (-5766497075 / 1000000000000) (-5766497074 / 1000000000000), orderedInterval (-30019089868 / 1000000000000) (-30019089867 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_stateChecks2 :
    compactCertificate563.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2006869535703571 / 4000000000000)) (orderedInterval (-5403888314 / 1000000000000) (-5403888311 / 1000000000000), orderedInterval (35214472627 / 1000000000000) (35214472630 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (3438805155423583 / 4000000000000)) (orderedInterval (-8297361025 / 1000000000000) (-8297361023 / 1000000000000), orderedInterval (25921358279 / 1000000000000) (25921358282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2533008313280797 / 4000000000000)) (orderedInterval (-16961212737 / 1000000000000) (-16961212277 / 1000000000000), orderedInterval (26802111512 / 1000000000000) (26802111972 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_stateChecks3 :
    compactCertificate563.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 309 12 (3886286144894131 / 4000000000000)) (orderedInterval (-25583115926 / 1000000000000) (-25583105013 / 1000000000000), orderedInterval (880233762 / 1000000000000) (880244675 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2243748351902299 / 4000000000000)) (orderedInterval (19651545776 / 1000000000000) (19651547227 / 1000000000000), orderedInterval (-27380608239 / 1000000000000) (-27380606788 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 317 12 (3981570824472791 / 4000000000000)) (orderedInterval (-7306902894 / 1000000000000) (-7306902893 / 1000000000000), orderedInterval (-24207394884 / 1000000000000) (-24207394883 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_stateChecks4 :
    compactCertificate563.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 296 12 (3720099940005779 / 4000000000000)) (orderedInterval (20475275081 / 1000000000000) (20475275082 / 1000000000000), orderedInterval (16276474633 / 1000000000000) (16276474634 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2654838852610307 / 4000000000000)) (orderedInterval (-30934907955 / 1000000000000) (-30934905489 / 1000000000000), orderedInterval (1511700299 / 1000000000000) (1511702765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3010304303554053 / 4000000000000)) (orderedInterval (-16921223368 / 1000000000000) (-16921222931 / 1000000000000), orderedInterval (23666961976 / 1000000000000) (23666962413 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_stateChecks5 :
    compactCertificate563.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2509677888303157 / 4000000000000)) (orderedInterval (-3619030850 / 1000000000000) (-3619030848 / 1000000000000), orderedInterval (31650421790 / 1000000000000) (31650421791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2217376525210297 / 4000000000000)) (orderedInterval (27218044230 / 1000000000000) (27218079650 / 1000000000000), orderedInterval (-20213592268 / 1000000000000) (-20213556848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (642682143407403 / 800000000000)) (orderedInterval (-3084653370 / 1000000000000) (-3084653369 / 1000000000000), orderedInterval (27982962107 / 1000000000000) (27982962108 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_stateChecks6 :
    compactCertificate563.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1777692631173041 / 4000000000000)) (orderedInterval (-29597392176 / 1000000000000) (-29597349408 / 1000000000000), orderedInterval (23622649308 / 1000000000000) (23622692076 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1506969730852201 / 4000000000000)) (orderedInterval (21006927767 / 1000000000000) (21006927768 / 1000000000000), orderedInterval (35306392439 / 1000000000000) (35306392440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (942991686719203 / 4000000000000)) (orderedInterval (-41133321149 / 1000000000000) (-41133321148 / 1000000000000), orderedInterval (-31669242581 / 1000000000000) (-31669242580 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_stateChecks7 :
    compactCertificate563.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (507144065366301 / 4000000000000)) (orderedInterval (66899546374 / 1000000000000) (66899549326 / 1000000000000), orderedInterval (-23622643100 / 1000000000000) (-23622640149 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1376994791041903 / 4000000000000)) (orderedInterval (-22163435550 / 1000000000000) (-22163433544 / 1000000000000), orderedInterval (36884394560 / 1000000000000) (36884396567 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1880168664262031 / 4000000000000)) (orderedInterval (-14723599770 / 1000000000000) (-14723599585 / 1000000000000), orderedInterval (33744059097 / 1000000000000) (33744059282 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_stateChecks8 :
    compactCertificate563.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (795008313280797 / 4000000000000)) (orderedInterval (-56536587114 / 1000000000000) (-56536586984 / 1000000000000), orderedInterval (2728555195 / 1000000000000) (2728555324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (3231664655944637 / 4000000000000)) (orderedInterval (-27136822151 / 1000000000000) (-27136822013 / 1000000000000), orderedInterval (-7164450238 / 1000000000000) (-7164450101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2158602221698483 / 4000000000000)) (orderedInterval (2805924057 / 1000000000000) (2805924058 / 1000000000000), orderedInterval (34229201158 / 1000000000000) (34229201159 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_states : ∀ j,
    BesselStateValid (compactCertificate563.point j) (compactCertificate563.state j) :=
  compactCertificate563.statesValid_of_checks3 compactCertificate563_stateChecks0
    compactCertificate563_stateChecks1 compactCertificate563_stateChecks2
    compactCertificate563_stateChecks3 compactCertificate563_stateChecks4
    compactCertificate563_stateChecks5 compactCertificate563_stateChecks6
    compactCertificate563_stateChecks7 compactCertificate563_stateChecks8

theorem compactCertificate563_chunkChecks0_0 :
    compactCertificate563.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (869 / 2) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37696137291 / 1000000000000) (37696140054 / 1000000000000), orderedInterval (-6690037590 / 1000000000000) (-6690034827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1280202933725969 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17091865911 / 1000000000000) (17091865912 / 1000000000000), orderedInterval (41167852065 / 1000000000000) (41167852066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (413991325337777 / 800000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3099138544 / 1000000000000) (3099138546 / 1000000000000), orderedInterval (-34940149655 / 1000000000000) (-34940149653 / 1000000000000)))) (orderedInterval (15282553193 / 1000000000000) (15282554319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (373560023189683 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-6080560071 / 1000000000000) (-6080560049 / 1000000000000), orderedInterval (82372764772 / 1000000000000) (82372764794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1003434767851351 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (15663850716 / 1000000000000) (15663850717 / 1000000000000), orderedInterval (47847901530 / 1000000000000) (47847901531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2724520590577467 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5766497075 / 1000000000000) (-5766497074 / 1000000000000), orderedInterval (-30019089868 / 1000000000000) (-30019089867 / 1000000000000)))) (orderedInterval (1047822485 / 1000000000000) (1047822538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2006869535703571 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5403888314 / 1000000000000) (-5403888311 / 1000000000000), orderedInterval (35214472627 / 1000000000000) (35214472630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3438805155423583 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8297361025 / 1000000000000) (-8297361023 / 1000000000000), orderedInterval (25921358279 / 1000000000000) (25921358282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2533008313280797 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16961212737 / 1000000000000) (-16961212277 / 1000000000000), orderedInterval (26802111512 / 1000000000000) (26802111972 / 1000000000000)))) (orderedInterval (-153995248 / 1000000000000) (-153995212 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks0_1 :
    compactCertificate563.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3886286144894131 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25583115926 / 1000000000000) (-25583105013 / 1000000000000), orderedInterval (880233762 / 1000000000000) (880244675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2243748351902299 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19651545776 / 1000000000000) (19651547227 / 1000000000000), orderedInterval (-27380608239 / 1000000000000) (-27380606788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3981570824472791 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7306902894 / 1000000000000) (-7306902893 / 1000000000000), orderedInterval (-24207394884 / 1000000000000) (-24207394883 / 1000000000000)))) (orderedInterval (4963107315 / 1000000000000) (4963109534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3720099940005779 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20475275081 / 1000000000000) (20475275082 / 1000000000000), orderedInterval (16276474633 / 1000000000000) (16276474634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2654838852610307 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30934907955 / 1000000000000) (-30934905489 / 1000000000000), orderedInterval (1511700299 / 1000000000000) (1511702765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3010304303554053 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16921223368 / 1000000000000) (-16921222931 / 1000000000000), orderedInterval (23666961976 / 1000000000000) (23666962413 / 1000000000000)))) (orderedInterval (-3209304349 / 1000000000000) (-3209304061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2509677888303157 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3619030850 / 1000000000000) (-3619030848 / 1000000000000), orderedInterval (31650421790 / 1000000000000) (31650421791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2217376525210297 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27218044230 / 1000000000000) (27218079650 / 1000000000000), orderedInterval (-20213592268 / 1000000000000) (-20213556848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (642682143407403 / 800000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3084653370 / 1000000000000) (-3084653369 / 1000000000000), orderedInterval (27982962107 / 1000000000000) (27982962108 / 1000000000000)))) (orderedInterval (-1678370958 / 1000000000000) (-1678368889 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks0_2 :
    compactCertificate563.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1777692631173041 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29597392176 / 1000000000000) (-29597349408 / 1000000000000), orderedInterval (23622649308 / 1000000000000) (23622692076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1506969730852201 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21006927767 / 1000000000000) (21006927768 / 1000000000000), orderedInterval (35306392439 / 1000000000000) (35306392440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (942991686719203 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41133321149 / 1000000000000) (-41133321148 / 1000000000000), orderedInterval (-31669242581 / 1000000000000) (-31669242580 / 1000000000000)))) (orderedInterval (2204294814 / 1000000000000) (2204301762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (507144065366301 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66899546374 / 1000000000000) (66899549326 / 1000000000000), orderedInterval (-23622643100 / 1000000000000) (-23622640149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1376994791041903 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22163435550 / 1000000000000) (-22163433544 / 1000000000000), orderedInterval (36884394560 / 1000000000000) (36884396567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1880168664262031 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14723599770 / 1000000000000) (-14723599585 / 1000000000000), orderedInterval (33744059097 / 1000000000000) (33744059282 / 1000000000000)))) (orderedInterval (395910761 / 1000000000000) (395910928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (795008313280797 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56536587114 / 1000000000000) (-56536586984 / 1000000000000), orderedInterval (2728555195 / 1000000000000) (2728555324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3231664655944637 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27136822151 / 1000000000000) (-27136822013 / 1000000000000), orderedInterval (-7164450238 / 1000000000000) (-7164450101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2158602221698483 / 4000000000000) 0 (IntervalRat.scale (869 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2805924057 / 1000000000000) (2805924058 / 1000000000000), orderedInterval (34229201158 / 1000000000000) (34229201159 / 1000000000000)))) (orderedInterval (1341698597 / 1000000000000) (1341698729 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks0 :
    compactCertificate563.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate563.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate563_chunkChecks0_0
    compactCertificate563_chunkChecks0_1 compactCertificate563_chunkChecks0_2

theorem compactCertificate563_chunkChecks1_0 :
    compactCertificate563.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (869 / 2) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37696137291 / 1000000000000) (37696140054 / 1000000000000), orderedInterval (-6690037590 / 1000000000000) (-6690034827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1280202933725969 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17091865911 / 1000000000000) (17091865912 / 1000000000000), orderedInterval (41167852065 / 1000000000000) (41167852066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (413991325337777 / 800000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3099138544 / 1000000000000) (3099138546 / 1000000000000), orderedInterval (-34940149655 / 1000000000000) (-34940149653 / 1000000000000)))) (orderedInterval (-4811074176 / 1000000000000) (-4811073046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (373560023189683 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-6080560071 / 1000000000000) (-6080560049 / 1000000000000), orderedInterval (82372764772 / 1000000000000) (82372764794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1003434767851351 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (15663850716 / 1000000000000) (15663850717 / 1000000000000), orderedInterval (47847901530 / 1000000000000) (47847901531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2724520590577467 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5766497075 / 1000000000000) (-5766497074 / 1000000000000), orderedInterval (-30019089868 / 1000000000000) (-30019089867 / 1000000000000)))) (orderedInterval (4161920999 / 1000000000000) (4161921059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2006869535703571 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5403888314 / 1000000000000) (-5403888311 / 1000000000000), orderedInterval (35214472627 / 1000000000000) (35214472630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3438805155423583 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8297361025 / 1000000000000) (-8297361023 / 1000000000000), orderedInterval (25921358279 / 1000000000000) (25921358282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2533008313280797 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16961212737 / 1000000000000) (-16961212277 / 1000000000000), orderedInterval (26802111512 / 1000000000000) (26802111972 / 1000000000000)))) (orderedInterval (-637871908 / 1000000000000) (-637871849 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks1_1 :
    compactCertificate563.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3886286144894131 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25583115926 / 1000000000000) (-25583105013 / 1000000000000), orderedInterval (880233762 / 1000000000000) (880244675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2243748351902299 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19651545776 / 1000000000000) (19651547227 / 1000000000000), orderedInterval (-27380608239 / 1000000000000) (-27380606788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3981570824472791 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7306902894 / 1000000000000) (-7306902893 / 1000000000000), orderedInterval (-24207394884 / 1000000000000) (-24207394883 / 1000000000000)))) (orderedInterval (-10852225871 / 1000000000000) (-10852221039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3720099940005779 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20475275081 / 1000000000000) (20475275082 / 1000000000000), orderedInterval (16276474633 / 1000000000000) (16276474634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2654838852610307 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30934907955 / 1000000000000) (-30934905489 / 1000000000000), orderedInterval (1511700299 / 1000000000000) (1511702765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3010304303554053 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16921223368 / 1000000000000) (-16921222931 / 1000000000000), orderedInterval (23666961976 / 1000000000000) (23666962413 / 1000000000000)))) (orderedInterval (-618035022 / 1000000000000) (-618034578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2509677888303157 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3619030850 / 1000000000000) (-3619030848 / 1000000000000), orderedInterval (31650421790 / 1000000000000) (31650421791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2217376525210297 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27218044230 / 1000000000000) (27218079650 / 1000000000000), orderedInterval (-20213592268 / 1000000000000) (-20213556848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (642682143407403 / 800000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3084653370 / 1000000000000) (-3084653369 / 1000000000000), orderedInterval (27982962107 / 1000000000000) (27982962108 / 1000000000000)))) (orderedInterval (3328277191 / 1000000000000) (3328279838 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks1_2 :
    compactCertificate563.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1777692631173041 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29597392176 / 1000000000000) (-29597349408 / 1000000000000), orderedInterval (23622649308 / 1000000000000) (23622692076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1506969730852201 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21006927767 / 1000000000000) (21006927768 / 1000000000000), orderedInterval (35306392439 / 1000000000000) (35306392440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (942991686719203 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41133321149 / 1000000000000) (-41133321148 / 1000000000000), orderedInterval (-31669242581 / 1000000000000) (-31669242580 / 1000000000000)))) (orderedInterval (-6155447901 / 1000000000000) (-6155440805 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (507144065366301 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66899546374 / 1000000000000) (66899549326 / 1000000000000), orderedInterval (-23622643100 / 1000000000000) (-23622640149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1376994791041903 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22163435550 / 1000000000000) (-22163433544 / 1000000000000), orderedInterval (36884394560 / 1000000000000) (36884396567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1880168664262031 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14723599770 / 1000000000000) (-14723599585 / 1000000000000), orderedInterval (33744059097 / 1000000000000) (33744059282 / 1000000000000)))) (orderedInterval (-3333348742 / 1000000000000) (-3333348628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (795008313280797 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56536587114 / 1000000000000) (-56536586984 / 1000000000000), orderedInterval (2728555195 / 1000000000000) (2728555324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3231664655944637 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27136822151 / 1000000000000) (-27136822013 / 1000000000000), orderedInterval (-7164450238 / 1000000000000) (-7164450101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2158602221698483 / 4000000000000) 1 (IntervalRat.scale (869 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2805924057 / 1000000000000) (2805924058 / 1000000000000), orderedInterval (34229201158 / 1000000000000) (34229201159 / 1000000000000)))) (orderedInterval (-6884593871 / 1000000000000) (-6884593681 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks1 :
    compactCertificate563.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate563.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate563_chunkChecks1_0
    compactCertificate563_chunkChecks1_1 compactCertificate563_chunkChecks1_2

theorem compactCertificate563_chunkChecks2_0 :
    compactCertificate563.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (869 / 2) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37696137291 / 1000000000000) (37696140054 / 1000000000000), orderedInterval (-6690037590 / 1000000000000) (-6690034827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1280202933725969 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17091865911 / 1000000000000) (17091865912 / 1000000000000), orderedInterval (41167852065 / 1000000000000) (41167852066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (413991325337777 / 800000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3099138544 / 1000000000000) (3099138546 / 1000000000000), orderedInterval (-34940149655 / 1000000000000) (-34940149653 / 1000000000000)))) (orderedInterval (-15274735454 / 1000000000000) (-15274734316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (373560023189683 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-6080560071 / 1000000000000) (-6080560049 / 1000000000000), orderedInterval (82372764772 / 1000000000000) (82372764794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1003434767851351 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (15663850716 / 1000000000000) (15663850717 / 1000000000000), orderedInterval (47847901530 / 1000000000000) (47847901531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2724520590577467 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5766497075 / 1000000000000) (-5766497074 / 1000000000000), orderedInterval (-30019089868 / 1000000000000) (-30019089867 / 1000000000000)))) (orderedInterval (-1210657785 / 1000000000000) (-1210657702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2006869535703571 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5403888314 / 1000000000000) (-5403888311 / 1000000000000), orderedInterval (35214472627 / 1000000000000) (35214472630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3438805155423583 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8297361025 / 1000000000000) (-8297361023 / 1000000000000), orderedInterval (25921358279 / 1000000000000) (25921358282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2533008313280797 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16961212737 / 1000000000000) (-16961212277 / 1000000000000), orderedInterval (26802111512 / 1000000000000) (26802111972 / 1000000000000)))) (orderedInterval (-129729919 / 1000000000000) (-129729819 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks2_1 :
    compactCertificate563.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3886286144894131 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25583115926 / 1000000000000) (-25583105013 / 1000000000000), orderedInterval (880233762 / 1000000000000) (880244675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2243748351902299 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19651545776 / 1000000000000) (19651547227 / 1000000000000), orderedInterval (-27380608239 / 1000000000000) (-27380606788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3981570824472791 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7306902894 / 1000000000000) (-7306902893 / 1000000000000), orderedInterval (-24207394884 / 1000000000000) (-24207394883 / 1000000000000)))) (orderedInterval (-19679380959 / 1000000000000) (-19679370308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3720099940005779 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20475275081 / 1000000000000) (20475275082 / 1000000000000), orderedInterval (16276474633 / 1000000000000) (16276474634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2654838852610307 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30934907955 / 1000000000000) (-30934905489 / 1000000000000), orderedInterval (1511700299 / 1000000000000) (1511702765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3010304303554053 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16921223368 / 1000000000000) (-16921222931 / 1000000000000), orderedInterval (23666961976 / 1000000000000) (23666962413 / 1000000000000)))) (orderedInterval (8263735436 / 1000000000000) (8263736127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2509677888303157 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3619030850 / 1000000000000) (-3619030848 / 1000000000000), orderedInterval (31650421790 / 1000000000000) (31650421791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2217376525210297 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27218044230 / 1000000000000) (27218079650 / 1000000000000), orderedInterval (-20213592268 / 1000000000000) (-20213556848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (642682143407403 / 800000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3084653370 / 1000000000000) (-3084653369 / 1000000000000), orderedInterval (27982962107 / 1000000000000) (27982962108 / 1000000000000)))) (orderedInterval (2884801887 / 1000000000000) (2884805282 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks2_2 :
    compactCertificate563.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1777692631173041 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29597392176 / 1000000000000) (-29597349408 / 1000000000000), orderedInterval (23622649308 / 1000000000000) (23622692076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1506969730852201 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21006927767 / 1000000000000) (21006927768 / 1000000000000), orderedInterval (35306392439 / 1000000000000) (35306392440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (942991686719203 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41133321149 / 1000000000000) (-41133321148 / 1000000000000), orderedInterval (-31669242581 / 1000000000000) (-31669242580 / 1000000000000)))) (orderedInterval (-3648747367 / 1000000000000) (-3648740101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (507144065366301 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66899546374 / 1000000000000) (66899549326 / 1000000000000), orderedInterval (-23622643100 / 1000000000000) (-23622640149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1376994791041903 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22163435550 / 1000000000000) (-22163433544 / 1000000000000), orderedInterval (36884394560 / 1000000000000) (36884396567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1880168664262031 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14723599770 / 1000000000000) (-14723599585 / 1000000000000), orderedInterval (33744059097 / 1000000000000) (33744059282 / 1000000000000)))) (orderedInterval (-1523332888 / 1000000000000) (-1523332791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (795008313280797 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56536587114 / 1000000000000) (-56536586984 / 1000000000000), orderedInterval (2728555195 / 1000000000000) (2728555324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3231664655944637 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27136822151 / 1000000000000) (-27136822013 / 1000000000000), orderedInterval (-7164450238 / 1000000000000) (-7164450101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2158602221698483 / 4000000000000) 2 (IntervalRat.scale (869 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2805924057 / 1000000000000) (2805924058 / 1000000000000), orderedInterval (34229201158 / 1000000000000) (34229201159 / 1000000000000)))) (orderedInterval (-6738136660 / 1000000000000) (-6738136371 / 1000000000000))) = true
  rfl'

theorem compactCertificate563_chunkChecks2 :
    compactCertificate563.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate563.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate563_chunkChecks2_0
    compactCertificate563_chunkChecks2_1 compactCertificate563_chunkChecks2_2

theorem compactCertificate563_chunkChecks3_0 :
    compactCertificate563.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (869 / 2) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37696137291 / 1000000000000) (37696140054 / 1000000000000), orderedInterval (-6690037590 / 1000000000000) (-6690034827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1280202933725969 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17091865911 / 1000000000000) (17091865912 / 1000000000000), orderedInterval (41167852065 / 1000000000000) (41167852066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (413991325337777 / 800000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3099138544 / 1000000000000) (3099138546 / 1000000000000), orderedInterval (-34940149655 / 1000000000000) (-34940149653 / 1000000000000)))) (orderedInterval (5997353914 / 1000000000000) (5997355058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (373560023189683 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-6080560071 / 1000000000000) (-6080560049 / 1000000000000), orderedInterval (82372764772 / 1000000000000) (82372764794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1003434767851351 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (15663850716 / 1000000000000) (15663850717 / 1000000000000), orderedInterval (47847901530 / 1000000000000) (47847901531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2724520590577467 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5766497075 / 1000000000000) (-5766497074 / 1000000000000), orderedInterval (-30019089868 / 1000000000000) (-30019089867 / 1000000000000)))) (orderedInterval (-8545533102 / 1000000000000) (-8545532979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2006869535703571 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5403888314 / 1000000000000) (-5403888311 / 1000000000000), orderedInterval (35214472627 / 1000000000000) (35214472630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3438805155423583 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8297361025 / 1000000000000) (-8297361023 / 1000000000000), orderedInterval (25921358279 / 1000000000000) (25921358282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2533008313280797 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16961212737 / 1000000000000) (-16961212277 / 1000000000000), orderedInterval (26802111512 / 1000000000000) (26802111972 / 1000000000000)))) (orderedInterval (4188045925 / 1000000000000) (4188046097 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate563_chunkChecks3_1 :
    compactCertificate563.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3886286144894131 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25583115926 / 1000000000000) (-25583105013 / 1000000000000), orderedInterval (880233762 / 1000000000000) (880244675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2243748351902299 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19651545776 / 1000000000000) (19651547227 / 1000000000000), orderedInterval (-27380608239 / 1000000000000) (-27380606788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3981570824472791 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7306902894 / 1000000000000) (-7306902893 / 1000000000000), orderedInterval (-24207394884 / 1000000000000) (-24207394883 / 1000000000000)))) (orderedInterval (47532881028 / 1000000000000) (47532904640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3720099940005779 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20475275081 / 1000000000000) (20475275082 / 1000000000000), orderedInterval (16276474633 / 1000000000000) (16276474634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2654838852610307 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30934907955 / 1000000000000) (-30934905489 / 1000000000000), orderedInterval (1511700299 / 1000000000000) (1511702765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3010304303554053 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16921223368 / 1000000000000) (-16921222931 / 1000000000000), orderedInterval (23666961976 / 1000000000000) (23666962413 / 1000000000000)))) (orderedInterval (2975354358 / 1000000000000) (2975355438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2509677888303157 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3619030850 / 1000000000000) (-3619030848 / 1000000000000), orderedInterval (31650421790 / 1000000000000) (31650421791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2217376525210297 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27218044230 / 1000000000000) (27218079650 / 1000000000000), orderedInterval (-20213592268 / 1000000000000) (-20213556848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (642682143407403 / 800000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3084653370 / 1000000000000) (-3084653369 / 1000000000000), orderedInterval (27982962107 / 1000000000000) (27982962108 / 1000000000000)))) (orderedInterval (-8037757944 / 1000000000000) (-8037753589 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate563_chunkChecks3_2 :
    compactCertificate563.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1777692631173041 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29597392176 / 1000000000000) (-29597349408 / 1000000000000), orderedInterval (23622649308 / 1000000000000) (23622692076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1506969730852201 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21006927767 / 1000000000000) (21006927768 / 1000000000000), orderedInterval (35306392439 / 1000000000000) (35306392440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (942991686719203 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41133321149 / 1000000000000) (-41133321148 / 1000000000000), orderedInterval (-31669242581 / 1000000000000) (-31669242580 / 1000000000000)))) (orderedInterval (5517532434 / 1000000000000) (5517539861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (507144065366301 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66899546374 / 1000000000000) (66899549326 / 1000000000000), orderedInterval (-23622643100 / 1000000000000) (-23622640149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1376994791041903 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22163435550 / 1000000000000) (-22163433544 / 1000000000000), orderedInterval (36884394560 / 1000000000000) (36884396567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1880168664262031 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14723599770 / 1000000000000) (-14723599585 / 1000000000000), orderedInterval (33744059097 / 1000000000000) (33744059282 / 1000000000000)))) (orderedInterval (3682881764 / 1000000000000) (3682881854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (795008313280797 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56536587114 / 1000000000000) (-56536586984 / 1000000000000), orderedInterval (2728555195 / 1000000000000) (2728555324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3231664655944637 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27136822151 / 1000000000000) (-27136822013 / 1000000000000), orderedInterval (-7164450238 / 1000000000000) (-7164450101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2158602221698483 / 4000000000000) 3 (IntervalRat.scale (869 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2805924057 / 1000000000000) (2805924058 / 1000000000000), orderedInterval (34229201158 / 1000000000000) (34229201159 / 1000000000000)))) (orderedInterval (8569005008 / 1000000000000) (8569005466 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate563_chunkChecks3 :
    compactCertificate563.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate563.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate563_chunkChecks3_0
    compactCertificate563_chunkChecks3_1 compactCertificate563_chunkChecks3_2

theorem compactCertificate563_chunkChecks4_0 :
    compactCertificate563.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (869 / 2) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37696137291 / 1000000000000) (37696140054 / 1000000000000), orderedInterval (-6690037590 / 1000000000000) (-6690034827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1280202933725969 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17091865911 / 1000000000000) (17091865912 / 1000000000000), orderedInterval (41167852065 / 1000000000000) (41167852066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (413991325337777 / 800000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3099138544 / 1000000000000) (3099138546 / 1000000000000), orderedInterval (-34940149655 / 1000000000000) (-34940149653 / 1000000000000)))) (orderedInterval (15326546636 / 1000000000000) (15326547789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (373560023189683 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-6080560071 / 1000000000000) (-6080560049 / 1000000000000), orderedInterval (82372764772 / 1000000000000) (82372764794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1003434767851351 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (15663850716 / 1000000000000) (15663850717 / 1000000000000), orderedInterval (47847901530 / 1000000000000) (47847901531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2724520590577467 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-5766497075 / 1000000000000) (-5766497074 / 1000000000000), orderedInterval (-30019089868 / 1000000000000) (-30019089867 / 1000000000000)))) (orderedInterval (2578610827 / 1000000000000) (2578611016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2006869535703571 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-5403888314 / 1000000000000) (-5403888311 / 1000000000000), orderedInterval (35214472627 / 1000000000000) (35214472630 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3438805155423583 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8297361025 / 1000000000000) (-8297361023 / 1000000000000), orderedInterval (25921358279 / 1000000000000) (25921358282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2533008313280797 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16961212737 / 1000000000000) (-16961212277 / 1000000000000), orderedInterval (26802111512 / 1000000000000) (26802111972 / 1000000000000)))) (orderedInterval (2053569118 / 1000000000000) (2053569423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate563_chunkChecks4_1 :
    compactCertificate563.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3886286144894131 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25583115926 / 1000000000000) (-25583105013 / 1000000000000), orderedInterval (880233762 / 1000000000000) (880244675 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2243748351902299 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19651545776 / 1000000000000) (19651547227 / 1000000000000), orderedInterval (-27380608239 / 1000000000000) (-27380606788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3981570824472791 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7306902894 / 1000000000000) (-7306902893 / 1000000000000), orderedInterval (-24207394884 / 1000000000000) (-24207394883 / 1000000000000)))) (orderedInterval (88860879702 / 1000000000000) (88860932305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3720099940005779 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20475275081 / 1000000000000) (20475275082 / 1000000000000), orderedInterval (16276474633 / 1000000000000) (16276474634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2654838852610307 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30934907955 / 1000000000000) (-30934905489 / 1000000000000), orderedInterval (1511700299 / 1000000000000) (1511702765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3010304303554053 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16921223368 / 1000000000000) (-16921222931 / 1000000000000), orderedInterval (23666961976 / 1000000000000) (23666962413 / 1000000000000)))) (orderedInterval (-22928476829 / 1000000000000) (-22928475126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2509677888303157 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-3619030850 / 1000000000000) (-3619030848 / 1000000000000), orderedInterval (31650421790 / 1000000000000) (31650421791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2217376525210297 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27218044230 / 1000000000000) (27218079650 / 1000000000000), orderedInterval (-20213592268 / 1000000000000) (-20213556848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (642682143407403 / 800000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3084653370 / 1000000000000) (-3084653369 / 1000000000000), orderedInterval (27982962107 / 1000000000000) (27982962108 / 1000000000000)))) (orderedInterval (-5194453417 / 1000000000000) (-5194447808 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate563_chunkChecks4_2 :
    compactCertificate563.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1777692631173041 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29597392176 / 1000000000000) (-29597349408 / 1000000000000), orderedInterval (23622649308 / 1000000000000) (23622692076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1506969730852201 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21006927767 / 1000000000000) (21006927768 / 1000000000000), orderedInterval (35306392439 / 1000000000000) (35306392440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (942991686719203 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41133321149 / 1000000000000) (-41133321148 / 1000000000000), orderedInterval (-31669242581 / 1000000000000) (-31669242580 / 1000000000000)))) (orderedInterval (4366233668 / 1000000000000) (4366241279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (507144065366301 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66899546374 / 1000000000000) (66899549326 / 1000000000000), orderedInterval (-23622643100 / 1000000000000) (-23622640149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1376994791041903 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22163435550 / 1000000000000) (-22163433544 / 1000000000000), orderedInterval (36884394560 / 1000000000000) (36884396567 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1880168664262031 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14723599770 / 1000000000000) (-14723599585 / 1000000000000), orderedInterval (33744059097 / 1000000000000) (33744059282 / 1000000000000)))) (orderedInterval (1717646754 / 1000000000000) (1717646842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (795008313280797 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56536587114 / 1000000000000) (-56536586984 / 1000000000000), orderedInterval (2728555195 / 1000000000000) (2728555324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3231664655944637 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27136822151 / 1000000000000) (-27136822013 / 1000000000000), orderedInterval (-7164450238 / 1000000000000) (-7164450101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2158602221698483 / 4000000000000) 4 (IntervalRat.scale (869 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2805924057 / 1000000000000) (2805924058 / 1000000000000), orderedInterval (34229201158 / 1000000000000) (34229201159 / 1000000000000)))) (orderedInterval (25098633890 / 1000000000000) (25098634643 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate563_chunkChecks4 :
    compactCertificate563.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate563.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate563_chunkChecks4_0
    compactCertificate563_chunkChecks4_1 compactCertificate563_chunkChecks4_2

theorem compactCertificate563_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate563.chunkCheck r b = true :=
  compactCertificate563.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate563_chunkChecks0
    · exact compactCertificate563_chunkChecks1
    · exact compactCertificate563_chunkChecks2
    · exact compactCertificate563_chunkChecks3
    · exact compactCertificate563_chunkChecks4)

theorem compactCertificate563_coefficient0 :
    compactCertificate563.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate563_coefficient1 :
    compactCertificate563.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate563_coefficient2 :
    compactCertificate563.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate563_coefficient3 :
    compactCertificate563.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate563_coefficient4 :
    compactCertificate563.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate563_coefficients : ∀ r : Fin 5,
    compactCertificate563.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate563_coefficient0
  · exact compactCertificate563_coefficient1
  · exact compactCertificate563_coefficient2
  · exact compactCertificate563_coefficient3
  · exact compactCertificate563_coefficient4

theorem compactCertificate563_lower : (1 : ℚ) ≤ compactCertificate563.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate563, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate563_proves {t : ℝ} (ht : t ∈ compactCertificate563.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate563.proves compactCertificate563_states compactCertificate563_chunks
    compactCertificate563_coefficients compactCertificate563_lower ht

end Erdos232
