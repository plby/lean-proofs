/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate387 : CompactCertificate where
  left := 258
  right := 259
  center := 517 / 2
  grid := fun i =>
    match i.val with
    | 0 => 82
    | 1 => 61
    | 2 => 98
    | 3 => 18
    | 4 => 48
    | 5 => 129
    | 6 => 95
    | 7 => 163
    | 8 => 120
    | 9 => 184
    | 10 => 106
    | 11 => 189
    | 12 => 176
    | 13 => 126
    | 14 => 143
    | 15 => 119
    | 16 => 105
    | 17 => 152
    | 18 => 84
    | 19 => 71
    | 20 => 45
    | 21 => 24
    | 22 => 65
    | 23 => 89
    | 24 => 38
    | 25 => 153
    | _ => 102
  point := fun i =>
    match i.val with
    | 0 => 517 / 2
    | 1 => 761639720064817 / 4000000000000
    | 2 => 246298636593361 / 800000000000
    | 3 => 222244570758419 / 4000000000000
    | 4 => 596980178341943 / 4000000000000
    | 5 => 1620917313381531 / 4000000000000
    | 6 => 1193960356684403 / 4000000000000
    | 7 => 2045871421581119 / 4000000000000
    | 8 => 1506979629420221 / 4000000000000
    | 9 => 2312094288734483 / 4000000000000
    | 10 => 1334888259992507 / 4000000000000
    | 11 => 2368782642407863 / 4000000000000
    | 12 => 2213224014940147 / 4000000000000
    | 13 => 1579461089527651 / 4000000000000
    | 14 => 1790940535025829 / 4000000000000
    | 15 => 1493099503167701 / 4000000000000
    | 16 => 1319198692213721 / 4000000000000
    | 17 => 382355199242379 / 800000000000
    | 18 => 1057614603356113 / 4000000000000
    | 19 => 896551612025993 / 4000000000000
    | 20 => 561020370579779 / 4000000000000
    | 21 => 301718621167293 / 4000000000000
    | 22 => 819224749100879 / 4000000000000
    | 23 => 1118581357219183 / 4000000000000
    | 24 => 472979629420221 / 4000000000000
    | 25 => 1922635934549341 / 4000000000000
    | _ => 1284231701516819 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (49360340388 / 1000000000000) (49360340804 / 1000000000000), orderedInterval (-5223632110 / 1000000000000) (-5223631694 / 1000000000000))
    | 1 => (orderedInterval (24758423610 / 1000000000000) (24758425186 / 1000000000000), orderedInterval (-52318670031 / 1000000000000) (-52318668456 / 1000000000000))
    | 2 => (orderedInterval (32051532474 / 1000000000000) (32051532475 / 1000000000000), orderedInterval (32204686493 / 1000000000000) (32204686494 / 1000000000000))
    | 3 => (orderedInterval (-21724441770 / 1000000000000) (-21724441583 / 1000000000000), orderedInterval (105011884558 / 1000000000000) (105011884745 / 1000000000000))
    | 4 => (orderedInterval (-45317288515 / 1000000000000) (-45317238294 / 1000000000000), orderedInterval (47183136051 / 1000000000000) (47183186272 / 1000000000000))
    | 5 => (orderedInterval (-26987402065 / 1000000000000) (-26987402064 / 1000000000000), orderedInterval (-28995847094 / 1000000000000) (-28995847093 / 1000000000000))
    | 6 => (orderedInterval (-33884365537 / 1000000000000) (-33884365536 / 1000000000000), orderedInterval (-31322372334 / 1000000000000) (-31322372333 / 1000000000000))
    | 7 => (orderedInterval (-6087202752 / 1000000000000) (-6087202751 / 1000000000000), orderedInterval (-34745138175 / 1000000000000) (-34745138174 / 1000000000000))
    | 8 => (orderedInterval (21094233751 / 1000000000000) (21094233752 / 1000000000000), orderedInterval (35254068023 / 1000000000000) (35254068024 / 1000000000000))
    | 9 => (orderedInterval (22759687359 / 1000000000000) (22759687360 / 1000000000000), orderedInterval (24133366775 / 1000000000000) (24133366776 / 1000000000000))
    | 10 => (orderedInterval (43561623760 / 1000000000000) (43561623824 / 1000000000000), orderedInterval (3099770459 / 1000000000000) (3099770523 / 1000000000000))
    | 11 => (orderedInterval (23062539777 / 1000000000000) (23062546554 / 1000000000000), orderedInterval (-23324733129 / 1000000000000) (-23324726352 / 1000000000000))
    | 12 => (orderedInterval (31243451593 / 1000000000000) (31243451596 / 1000000000000), orderedInterval (13178616856 / 1000000000000) (13178616859 / 1000000000000))
    | 13 => (orderedInterval (-7595837984 / 1000000000000) (-7595837972 / 1000000000000), orderedInterval (39437400080 / 1000000000000) (39437400093 / 1000000000000))
    | 14 => (orderedInterval (25075657391 / 1000000000000) (25075665746 / 1000000000000), orderedInterval (-28189651075 / 1000000000000) (-28189642720 / 1000000000000))
    | 15 => (orderedInterval (-8625599745 / 1000000000000) (-8625599744 / 1000000000000), orderedInterval (-40375312874 / 1000000000000) (-40375312873 / 1000000000000))
    | 16 => (orderedInterval (-28886463585 / 1000000000000) (-28886463584 / 1000000000000), orderedInterval (-33060513304 / 1000000000000) (-33060513303 / 1000000000000))
    | 17 => (orderedInterval (34108600614 / 1000000000000) (34108600616 / 1000000000000), orderedInterval (12948900577 / 1000000000000) (12948900579 / 1000000000000))
    | 18 => (orderedInterval (47211717221 / 1000000000000) (47211717223 / 1000000000000), orderedInterval (13282601992 / 1000000000000) (13282601994 / 1000000000000))
    | 19 => (orderedInterval (-50931904919 / 1000000000000) (-50931901559 / 1000000000000), orderedInterval (15805630175 / 1000000000000) (15805633535 / 1000000000000))
    | 20 => (orderedInterval (21963298985 / 1000000000000) (21963299555 / 1000000000000), orderedInterval (-63770131533 / 1000000000000) (-63770130963 / 1000000000000))
    | 21 => (orderedInterval (66865574220 / 1000000000000) (66865574221 / 1000000000000), orderedInterval (62555974933 / 1000000000000) (62555974934 / 1000000000000))
    | 22 => (orderedInterval (-54818510100 / 1000000000000) (-54818510095 / 1000000000000), orderedInterval (-10030981313 / 1000000000000) (-10030981309 / 1000000000000))
    | 23 => (orderedInterval (-35161943428 / 1000000000000) (-35161943427 / 1000000000000), orderedInterval (-32188689727 / 1000000000000) (-32188689726 / 1000000000000))
    | 24 => (orderedInterval (-25247738393 / 1000000000000) (-25247737569 / 1000000000000), orderedInterval (69001583997 / 1000000000000) (69001584821 / 1000000000000))
    | 25 => (orderedInterval (-25606187315 / 1000000000000) (-25606187314 / 1000000000000), orderedInterval (-25834454435 / 1000000000000) (-25834454434 / 1000000000000))
    | _ => (orderedInterval (43885266809 / 1000000000000) (43885266822 / 1000000000000), orderedInterval (7479001911 / 1000000000000) (7479001924 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (21676231904 / 1000000000000) (21676232102 / 1000000000000)
      | 1 => orderedInterval (499606169 / 1000000000000) (499608037 / 1000000000000)
      | 2 => orderedInterval (697559691 / 1000000000000) (697559706 / 1000000000000)
      | 3 => orderedInterval (2461912071 / 1000000000000) (2461913142 / 1000000000000)
      | 4 => orderedInterval (-1409222256 / 1000000000000) (-1409222181 / 1000000000000)
      | 5 => orderedInterval (2426785634 / 1000000000000) (2426785659 / 1000000000000)
      | 6 => orderedInterval (-3951032253 / 1000000000000) (-3951031978 / 1000000000000)
      | 7 => orderedInterval (2703750918 / 1000000000000) (2703750949 / 1000000000000)
      | _ => orderedInterval (-6301852735 / 1000000000000) (-6301852655 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-178801977 / 1000000000000) (-178801781 / 1000000000000)
      | 1 => orderedInterval (3981083668 / 1000000000000) (3981084763 / 1000000000000)
      | 2 => orderedInterval (3362182086 / 1000000000000) (3362182112 / 1000000000000)
      | 3 => orderedInterval (-16888247138 / 1000000000000) (-16888244711 / 1000000000000)
      | 4 => orderedInterval (5434463477 / 1000000000000) (5434463602 / 1000000000000)
      | 5 => orderedInterval (2353521464 / 1000000000000) (2353521501 / 1000000000000)
      | 6 => orderedInterval (-4074381862 / 1000000000000) (-4074381626 / 1000000000000)
      | 7 => orderedInterval (2511943621 / 1000000000000) (2511943650 / 1000000000000)
      | _ => orderedInterval (2357716913 / 1000000000000) (2357717019 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-22357095845 / 1000000000000) (-22357095648 / 1000000000000)
      | 1 => orderedInterval (-4189386819 / 1000000000000) (-4189386154 / 1000000000000)
      | 2 => orderedInterval (-1830910620 / 1000000000000) (-1830910574 / 1000000000000)
      | 3 => orderedInterval (-2299384931 / 1000000000000) (-2299379402 / 1000000000000)
      | 4 => orderedInterval (4619829515 / 1000000000000) (4619829728 / 1000000000000)
      | 5 => orderedInterval (-5477564372 / 1000000000000) (-5477564318 / 1000000000000)
      | 6 => orderedInterval (5535521854 / 1000000000000) (5535522061 / 1000000000000)
      | 7 => orderedInterval (-3838926635 / 1000000000000) (-3838926607 / 1000000000000)
      | _ => orderedInterval (5517709422 / 1000000000000) (5517709576 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-840869446 / 1000000000000) (-840869247 / 1000000000000)
      | 1 => orderedInterval (-8244741289 / 1000000000000) (-8244740860 / 1000000000000)
      | 2 => orderedInterval (-10931626962 / 1000000000000) (-10931626879 / 1000000000000)
      | 3 => orderedInterval (87323435014 / 1000000000000) (87323447626 / 1000000000000)
      | 4 => orderedInterval (-11718053710 / 1000000000000) (-11718053344 / 1000000000000)
      | 5 => orderedInterval (-4599407270 / 1000000000000) (-4599407187 / 1000000000000)
      | 6 => orderedInterval (3165935740 / 1000000000000) (3165935924 / 1000000000000)
      | 7 => orderedInterval (-3192746375 / 1000000000000) (-3192746345 / 1000000000000)
      | _ => orderedInterval (-10892210359 / 1000000000000) (-10892210124 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (23423163885 / 1000000000000) (23423164088 / 1000000000000)
      | 1 => orderedInterval (11466254247 / 1000000000000) (11466254567 / 1000000000000)
      | 2 => orderedInterval (5262208105 / 1000000000000) (5262208257 / 1000000000000)
      | 3 => orderedInterval (-2512642429 / 1000000000000) (-2512613572 / 1000000000000)
      | 4 => orderedInterval (-16801406506 / 1000000000000) (-16801405873 / 1000000000000)
      | 5 => orderedInterval (14187765248 / 1000000000000) (14187765379 / 1000000000000)
      | 6 => orderedInterval (-6595439260 / 1000000000000) (-6595439094 / 1000000000000)
      | 7 => orderedInterval (4196445205 / 1000000000000) (4196445236 / 1000000000000)
      | _ => orderedInterval (5400911750 / 1000000000000) (5400912126 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (18803739143 / 1000000000000) (18803742781 / 1000000000000)
    | 1 => orderedInterval (-1140519748 / 1000000000000) (-1140515471 / 1000000000000)
    | 2 => orderedInterval (-24320208431 / 1000000000000) (-24320201338 / 1000000000000)
    | 3 => orderedInterval (40069715343 / 1000000000000) (40069729564 / 1000000000000)
    | _ => orderedInterval (38027260245 / 1000000000000) (38027291114 / 1000000000000)

theorem compactCertificate387_stateChecks0 :
    compactCertificate387.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (517 / 2)) (orderedInterval (49360340388 / 1000000000000) (49360340804 / 1000000000000), orderedInterval (-5223632110 / 1000000000000) (-5223631694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (761639720064817 / 4000000000000)) (orderedInterval (24758423610 / 1000000000000) (24758425186 / 1000000000000), orderedInterval (-52318670031 / 1000000000000) (-52318668456 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (246298636593361 / 800000000000)) (orderedInterval (32051532474 / 1000000000000) (32051532475 / 1000000000000), orderedInterval (32204686493 / 1000000000000) (32204686494 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_stateChecks1 :
    compactCertificate387.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (222244570758419 / 4000000000000)) (orderedInterval (-21724441770 / 1000000000000) (-21724441583 / 1000000000000), orderedInterval (105011884558 / 1000000000000) (105011884745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (596980178341943 / 4000000000000)) (orderedInterval (-45317288515 / 1000000000000) (-45317238294 / 1000000000000), orderedInterval (47183136051 / 1000000000000) (47183186272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1620917313381531 / 4000000000000)) (orderedInterval (-26987402065 / 1000000000000) (-26987402064 / 1000000000000), orderedInterval (-28995847094 / 1000000000000) (-28995847093 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_stateChecks2 :
    compactCertificate387.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1193960356684403 / 4000000000000)) (orderedInterval (-33884365537 / 1000000000000) (-33884365536 / 1000000000000), orderedInterval (-31322372334 / 1000000000000) (-31322372333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2045871421581119 / 4000000000000)) (orderedInterval (-6087202752 / 1000000000000) (-6087202751 / 1000000000000), orderedInterval (-34745138175 / 1000000000000) (-34745138174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1506979629420221 / 4000000000000)) (orderedInterval (21094233751 / 1000000000000) (21094233752 / 1000000000000), orderedInterval (35254068023 / 1000000000000) (35254068024 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_stateChecks3 :
    compactCertificate387.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2312094288734483 / 4000000000000)) (orderedInterval (22759687359 / 1000000000000) (22759687360 / 1000000000000), orderedInterval (24133366775 / 1000000000000) (24133366776 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1334888259992507 / 4000000000000)) (orderedInterval (43561623760 / 1000000000000) (43561623824 / 1000000000000), orderedInterval (3099770459 / 1000000000000) (3099770523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2368782642407863 / 4000000000000)) (orderedInterval (23062539777 / 1000000000000) (23062546554 / 1000000000000), orderedInterval (-23324733129 / 1000000000000) (-23324726352 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_stateChecks4 :
    compactCertificate387.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2213224014940147 / 4000000000000)) (orderedInterval (31243451593 / 1000000000000) (31243451596 / 1000000000000), orderedInterval (13178616856 / 1000000000000) (13178616859 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1579461089527651 / 4000000000000)) (orderedInterval (-7595837984 / 1000000000000) (-7595837972 / 1000000000000), orderedInterval (39437400080 / 1000000000000) (39437400093 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1790940535025829 / 4000000000000)) (orderedInterval (25075657391 / 1000000000000) (25075665746 / 1000000000000), orderedInterval (-28189651075 / 1000000000000) (-28189642720 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_stateChecks5 :
    compactCertificate387.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1493099503167701 / 4000000000000)) (orderedInterval (-8625599745 / 1000000000000) (-8625599744 / 1000000000000), orderedInterval (-40375312874 / 1000000000000) (-40375312873 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1319198692213721 / 4000000000000)) (orderedInterval (-28886463585 / 1000000000000) (-28886463584 / 1000000000000), orderedInterval (-33060513304 / 1000000000000) (-33060513303 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (382355199242379 / 800000000000)) (orderedInterval (34108600614 / 1000000000000) (34108600616 / 1000000000000), orderedInterval (12948900577 / 1000000000000) (12948900579 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_stateChecks6 :
    compactCertificate387.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1057614603356113 / 4000000000000)) (orderedInterval (47211717221 / 1000000000000) (47211717223 / 1000000000000), orderedInterval (13282601992 / 1000000000000) (13282601994 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (896551612025993 / 4000000000000)) (orderedInterval (-50931904919 / 1000000000000) (-50931901559 / 1000000000000), orderedInterval (15805630175 / 1000000000000) (15805633535 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (561020370579779 / 4000000000000)) (orderedInterval (21963298985 / 1000000000000) (21963299555 / 1000000000000), orderedInterval (-63770131533 / 1000000000000) (-63770130963 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_stateChecks7 :
    compactCertificate387.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (301718621167293 / 4000000000000)) (orderedInterval (66865574220 / 1000000000000) (66865574221 / 1000000000000), orderedInterval (62555974933 / 1000000000000) (62555974934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (819224749100879 / 4000000000000)) (orderedInterval (-54818510100 / 1000000000000) (-54818510095 / 1000000000000), orderedInterval (-10030981313 / 1000000000000) (-10030981309 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1118581357219183 / 4000000000000)) (orderedInterval (-35161943428 / 1000000000000) (-35161943427 / 1000000000000), orderedInterval (-32188689727 / 1000000000000) (-32188689726 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_stateChecks8 :
    compactCertificate387.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (472979629420221 / 4000000000000)) (orderedInterval (-25247738393 / 1000000000000) (-25247737569 / 1000000000000), orderedInterval (69001583997 / 1000000000000) (69001584821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1922635934549341 / 4000000000000)) (orderedInterval (-25606187315 / 1000000000000) (-25606187314 / 1000000000000), orderedInterval (-25834454435 / 1000000000000) (-25834454434 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1284231701516819 / 4000000000000)) (orderedInterval (43885266809 / 1000000000000) (43885266822 / 1000000000000), orderedInterval (7479001911 / 1000000000000) (7479001924 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_states : ∀ j,
    BesselStateValid (compactCertificate387.point j) (compactCertificate387.state j) :=
  compactCertificate387.statesValid_of_checks3 compactCertificate387_stateChecks0
    compactCertificate387_stateChecks1 compactCertificate387_stateChecks2
    compactCertificate387_stateChecks3 compactCertificate387_stateChecks4
    compactCertificate387_stateChecks5 compactCertificate387_stateChecks6
    compactCertificate387_stateChecks7 compactCertificate387_stateChecks8

theorem compactCertificate387_chunkChecks0_0 :
    compactCertificate387.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (517 / 2) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49360340388 / 1000000000000) (49360340804 / 1000000000000), orderedInterval (-5223632110 / 1000000000000) (-5223631694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (761639720064817 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24758423610 / 1000000000000) (24758425186 / 1000000000000), orderedInterval (-52318670031 / 1000000000000) (-52318668456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (246298636593361 / 800000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32051532474 / 1000000000000) (32051532475 / 1000000000000), orderedInterval (32204686493 / 1000000000000) (32204686494 / 1000000000000)))) (orderedInterval (21676231904 / 1000000000000) (21676232102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (222244570758419 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-21724441770 / 1000000000000) (-21724441583 / 1000000000000), orderedInterval (105011884558 / 1000000000000) (105011884745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (596980178341943 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45317288515 / 1000000000000) (-45317238294 / 1000000000000), orderedInterval (47183136051 / 1000000000000) (47183186272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1620917313381531 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26987402065 / 1000000000000) (-26987402064 / 1000000000000), orderedInterval (-28995847094 / 1000000000000) (-28995847093 / 1000000000000)))) (orderedInterval (499606169 / 1000000000000) (499608037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1193960356684403 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33884365537 / 1000000000000) (-33884365536 / 1000000000000), orderedInterval (-31322372334 / 1000000000000) (-31322372333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2045871421581119 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6087202752 / 1000000000000) (-6087202751 / 1000000000000), orderedInterval (-34745138175 / 1000000000000) (-34745138174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1506979629420221 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21094233751 / 1000000000000) (21094233752 / 1000000000000), orderedInterval (35254068023 / 1000000000000) (35254068024 / 1000000000000)))) (orderedInterval (697559691 / 1000000000000) (697559706 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks0_1 :
    compactCertificate387.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2312094288734483 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22759687359 / 1000000000000) (22759687360 / 1000000000000), orderedInterval (24133366775 / 1000000000000) (24133366776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1334888259992507 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43561623760 / 1000000000000) (43561623824 / 1000000000000), orderedInterval (3099770459 / 1000000000000) (3099770523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2368782642407863 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23062539777 / 1000000000000) (23062546554 / 1000000000000), orderedInterval (-23324733129 / 1000000000000) (-23324726352 / 1000000000000)))) (orderedInterval (2461912071 / 1000000000000) (2461913142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2213224014940147 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31243451593 / 1000000000000) (31243451596 / 1000000000000), orderedInterval (13178616856 / 1000000000000) (13178616859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1579461089527651 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-7595837984 / 1000000000000) (-7595837972 / 1000000000000), orderedInterval (39437400080 / 1000000000000) (39437400093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1790940535025829 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25075657391 / 1000000000000) (25075665746 / 1000000000000), orderedInterval (-28189651075 / 1000000000000) (-28189642720 / 1000000000000)))) (orderedInterval (-1409222256 / 1000000000000) (-1409222181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1493099503167701 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8625599745 / 1000000000000) (-8625599744 / 1000000000000), orderedInterval (-40375312874 / 1000000000000) (-40375312873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1319198692213721 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28886463585 / 1000000000000) (-28886463584 / 1000000000000), orderedInterval (-33060513304 / 1000000000000) (-33060513303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (382355199242379 / 800000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34108600614 / 1000000000000) (34108600616 / 1000000000000), orderedInterval (12948900577 / 1000000000000) (12948900579 / 1000000000000)))) (orderedInterval (2426785634 / 1000000000000) (2426785659 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks0_2 :
    compactCertificate387.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1057614603356113 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47211717221 / 1000000000000) (47211717223 / 1000000000000), orderedInterval (13282601992 / 1000000000000) (13282601994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (896551612025993 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50931904919 / 1000000000000) (-50931901559 / 1000000000000), orderedInterval (15805630175 / 1000000000000) (15805633535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (561020370579779 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21963298985 / 1000000000000) (21963299555 / 1000000000000), orderedInterval (-63770131533 / 1000000000000) (-63770130963 / 1000000000000)))) (orderedInterval (-3951032253 / 1000000000000) (-3951031978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (301718621167293 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66865574220 / 1000000000000) (66865574221 / 1000000000000), orderedInterval (62555974933 / 1000000000000) (62555974934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (819224749100879 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54818510100 / 1000000000000) (-54818510095 / 1000000000000), orderedInterval (-10030981313 / 1000000000000) (-10030981309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1118581357219183 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35161943428 / 1000000000000) (-35161943427 / 1000000000000), orderedInterval (-32188689727 / 1000000000000) (-32188689726 / 1000000000000)))) (orderedInterval (2703750918 / 1000000000000) (2703750949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (472979629420221 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25247738393 / 1000000000000) (-25247737569 / 1000000000000), orderedInterval (69001583997 / 1000000000000) (69001584821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1922635934549341 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25606187315 / 1000000000000) (-25606187314 / 1000000000000), orderedInterval (-25834454435 / 1000000000000) (-25834454434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1284231701516819 / 4000000000000) 0 (IntervalRat.scale (517 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43885266809 / 1000000000000) (43885266822 / 1000000000000), orderedInterval (7479001911 / 1000000000000) (7479001924 / 1000000000000)))) (orderedInterval (-6301852735 / 1000000000000) (-6301852655 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks0 :
    compactCertificate387.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate387.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate387_chunkChecks0_0
    compactCertificate387_chunkChecks0_1 compactCertificate387_chunkChecks0_2

theorem compactCertificate387_chunkChecks1_0 :
    compactCertificate387.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (517 / 2) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49360340388 / 1000000000000) (49360340804 / 1000000000000), orderedInterval (-5223632110 / 1000000000000) (-5223631694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (761639720064817 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24758423610 / 1000000000000) (24758425186 / 1000000000000), orderedInterval (-52318670031 / 1000000000000) (-52318668456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (246298636593361 / 800000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32051532474 / 1000000000000) (32051532475 / 1000000000000), orderedInterval (32204686493 / 1000000000000) (32204686494 / 1000000000000)))) (orderedInterval (-178801977 / 1000000000000) (-178801781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (222244570758419 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-21724441770 / 1000000000000) (-21724441583 / 1000000000000), orderedInterval (105011884558 / 1000000000000) (105011884745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (596980178341943 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45317288515 / 1000000000000) (-45317238294 / 1000000000000), orderedInterval (47183136051 / 1000000000000) (47183186272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1620917313381531 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26987402065 / 1000000000000) (-26987402064 / 1000000000000), orderedInterval (-28995847094 / 1000000000000) (-28995847093 / 1000000000000)))) (orderedInterval (3981083668 / 1000000000000) (3981084763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1193960356684403 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33884365537 / 1000000000000) (-33884365536 / 1000000000000), orderedInterval (-31322372334 / 1000000000000) (-31322372333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2045871421581119 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6087202752 / 1000000000000) (-6087202751 / 1000000000000), orderedInterval (-34745138175 / 1000000000000) (-34745138174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1506979629420221 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21094233751 / 1000000000000) (21094233752 / 1000000000000), orderedInterval (35254068023 / 1000000000000) (35254068024 / 1000000000000)))) (orderedInterval (3362182086 / 1000000000000) (3362182112 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks1_1 :
    compactCertificate387.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2312094288734483 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22759687359 / 1000000000000) (22759687360 / 1000000000000), orderedInterval (24133366775 / 1000000000000) (24133366776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1334888259992507 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43561623760 / 1000000000000) (43561623824 / 1000000000000), orderedInterval (3099770459 / 1000000000000) (3099770523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2368782642407863 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23062539777 / 1000000000000) (23062546554 / 1000000000000), orderedInterval (-23324733129 / 1000000000000) (-23324726352 / 1000000000000)))) (orderedInterval (-16888247138 / 1000000000000) (-16888244711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2213224014940147 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31243451593 / 1000000000000) (31243451596 / 1000000000000), orderedInterval (13178616856 / 1000000000000) (13178616859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1579461089527651 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-7595837984 / 1000000000000) (-7595837972 / 1000000000000), orderedInterval (39437400080 / 1000000000000) (39437400093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1790940535025829 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25075657391 / 1000000000000) (25075665746 / 1000000000000), orderedInterval (-28189651075 / 1000000000000) (-28189642720 / 1000000000000)))) (orderedInterval (5434463477 / 1000000000000) (5434463602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1493099503167701 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8625599745 / 1000000000000) (-8625599744 / 1000000000000), orderedInterval (-40375312874 / 1000000000000) (-40375312873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1319198692213721 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28886463585 / 1000000000000) (-28886463584 / 1000000000000), orderedInterval (-33060513304 / 1000000000000) (-33060513303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (382355199242379 / 800000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34108600614 / 1000000000000) (34108600616 / 1000000000000), orderedInterval (12948900577 / 1000000000000) (12948900579 / 1000000000000)))) (orderedInterval (2353521464 / 1000000000000) (2353521501 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks1_2 :
    compactCertificate387.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1057614603356113 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47211717221 / 1000000000000) (47211717223 / 1000000000000), orderedInterval (13282601992 / 1000000000000) (13282601994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (896551612025993 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50931904919 / 1000000000000) (-50931901559 / 1000000000000), orderedInterval (15805630175 / 1000000000000) (15805633535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (561020370579779 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21963298985 / 1000000000000) (21963299555 / 1000000000000), orderedInterval (-63770131533 / 1000000000000) (-63770130963 / 1000000000000)))) (orderedInterval (-4074381862 / 1000000000000) (-4074381626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (301718621167293 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66865574220 / 1000000000000) (66865574221 / 1000000000000), orderedInterval (62555974933 / 1000000000000) (62555974934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (819224749100879 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54818510100 / 1000000000000) (-54818510095 / 1000000000000), orderedInterval (-10030981313 / 1000000000000) (-10030981309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1118581357219183 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35161943428 / 1000000000000) (-35161943427 / 1000000000000), orderedInterval (-32188689727 / 1000000000000) (-32188689726 / 1000000000000)))) (orderedInterval (2511943621 / 1000000000000) (2511943650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (472979629420221 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25247738393 / 1000000000000) (-25247737569 / 1000000000000), orderedInterval (69001583997 / 1000000000000) (69001584821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1922635934549341 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25606187315 / 1000000000000) (-25606187314 / 1000000000000), orderedInterval (-25834454435 / 1000000000000) (-25834454434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1284231701516819 / 4000000000000) 1 (IntervalRat.scale (517 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43885266809 / 1000000000000) (43885266822 / 1000000000000), orderedInterval (7479001911 / 1000000000000) (7479001924 / 1000000000000)))) (orderedInterval (2357716913 / 1000000000000) (2357717019 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks1 :
    compactCertificate387.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate387.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate387_chunkChecks1_0
    compactCertificate387_chunkChecks1_1 compactCertificate387_chunkChecks1_2

theorem compactCertificate387_chunkChecks2_0 :
    compactCertificate387.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (517 / 2) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49360340388 / 1000000000000) (49360340804 / 1000000000000), orderedInterval (-5223632110 / 1000000000000) (-5223631694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (761639720064817 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24758423610 / 1000000000000) (24758425186 / 1000000000000), orderedInterval (-52318670031 / 1000000000000) (-52318668456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (246298636593361 / 800000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32051532474 / 1000000000000) (32051532475 / 1000000000000), orderedInterval (32204686493 / 1000000000000) (32204686494 / 1000000000000)))) (orderedInterval (-22357095845 / 1000000000000) (-22357095648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (222244570758419 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-21724441770 / 1000000000000) (-21724441583 / 1000000000000), orderedInterval (105011884558 / 1000000000000) (105011884745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (596980178341943 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45317288515 / 1000000000000) (-45317238294 / 1000000000000), orderedInterval (47183136051 / 1000000000000) (47183186272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1620917313381531 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26987402065 / 1000000000000) (-26987402064 / 1000000000000), orderedInterval (-28995847094 / 1000000000000) (-28995847093 / 1000000000000)))) (orderedInterval (-4189386819 / 1000000000000) (-4189386154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1193960356684403 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33884365537 / 1000000000000) (-33884365536 / 1000000000000), orderedInterval (-31322372334 / 1000000000000) (-31322372333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2045871421581119 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6087202752 / 1000000000000) (-6087202751 / 1000000000000), orderedInterval (-34745138175 / 1000000000000) (-34745138174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1506979629420221 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21094233751 / 1000000000000) (21094233752 / 1000000000000), orderedInterval (35254068023 / 1000000000000) (35254068024 / 1000000000000)))) (orderedInterval (-1830910620 / 1000000000000) (-1830910574 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks2_1 :
    compactCertificate387.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2312094288734483 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22759687359 / 1000000000000) (22759687360 / 1000000000000), orderedInterval (24133366775 / 1000000000000) (24133366776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1334888259992507 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43561623760 / 1000000000000) (43561623824 / 1000000000000), orderedInterval (3099770459 / 1000000000000) (3099770523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2368782642407863 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23062539777 / 1000000000000) (23062546554 / 1000000000000), orderedInterval (-23324733129 / 1000000000000) (-23324726352 / 1000000000000)))) (orderedInterval (-2299384931 / 1000000000000) (-2299379402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2213224014940147 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31243451593 / 1000000000000) (31243451596 / 1000000000000), orderedInterval (13178616856 / 1000000000000) (13178616859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1579461089527651 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-7595837984 / 1000000000000) (-7595837972 / 1000000000000), orderedInterval (39437400080 / 1000000000000) (39437400093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1790940535025829 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25075657391 / 1000000000000) (25075665746 / 1000000000000), orderedInterval (-28189651075 / 1000000000000) (-28189642720 / 1000000000000)))) (orderedInterval (4619829515 / 1000000000000) (4619829728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1493099503167701 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8625599745 / 1000000000000) (-8625599744 / 1000000000000), orderedInterval (-40375312874 / 1000000000000) (-40375312873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1319198692213721 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28886463585 / 1000000000000) (-28886463584 / 1000000000000), orderedInterval (-33060513304 / 1000000000000) (-33060513303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (382355199242379 / 800000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34108600614 / 1000000000000) (34108600616 / 1000000000000), orderedInterval (12948900577 / 1000000000000) (12948900579 / 1000000000000)))) (orderedInterval (-5477564372 / 1000000000000) (-5477564318 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks2_2 :
    compactCertificate387.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1057614603356113 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47211717221 / 1000000000000) (47211717223 / 1000000000000), orderedInterval (13282601992 / 1000000000000) (13282601994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (896551612025993 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50931904919 / 1000000000000) (-50931901559 / 1000000000000), orderedInterval (15805630175 / 1000000000000) (15805633535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (561020370579779 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21963298985 / 1000000000000) (21963299555 / 1000000000000), orderedInterval (-63770131533 / 1000000000000) (-63770130963 / 1000000000000)))) (orderedInterval (5535521854 / 1000000000000) (5535522061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (301718621167293 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66865574220 / 1000000000000) (66865574221 / 1000000000000), orderedInterval (62555974933 / 1000000000000) (62555974934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (819224749100879 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54818510100 / 1000000000000) (-54818510095 / 1000000000000), orderedInterval (-10030981313 / 1000000000000) (-10030981309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1118581357219183 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35161943428 / 1000000000000) (-35161943427 / 1000000000000), orderedInterval (-32188689727 / 1000000000000) (-32188689726 / 1000000000000)))) (orderedInterval (-3838926635 / 1000000000000) (-3838926607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (472979629420221 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25247738393 / 1000000000000) (-25247737569 / 1000000000000), orderedInterval (69001583997 / 1000000000000) (69001584821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1922635934549341 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25606187315 / 1000000000000) (-25606187314 / 1000000000000), orderedInterval (-25834454435 / 1000000000000) (-25834454434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1284231701516819 / 4000000000000) 2 (IntervalRat.scale (517 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43885266809 / 1000000000000) (43885266822 / 1000000000000), orderedInterval (7479001911 / 1000000000000) (7479001924 / 1000000000000)))) (orderedInterval (5517709422 / 1000000000000) (5517709576 / 1000000000000))) = true
  rfl'

theorem compactCertificate387_chunkChecks2 :
    compactCertificate387.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate387.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate387_chunkChecks2_0
    compactCertificate387_chunkChecks2_1 compactCertificate387_chunkChecks2_2

theorem compactCertificate387_chunkChecks3_0 :
    compactCertificate387.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (517 / 2) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49360340388 / 1000000000000) (49360340804 / 1000000000000), orderedInterval (-5223632110 / 1000000000000) (-5223631694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (761639720064817 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24758423610 / 1000000000000) (24758425186 / 1000000000000), orderedInterval (-52318670031 / 1000000000000) (-52318668456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (246298636593361 / 800000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32051532474 / 1000000000000) (32051532475 / 1000000000000), orderedInterval (32204686493 / 1000000000000) (32204686494 / 1000000000000)))) (orderedInterval (-840869446 / 1000000000000) (-840869247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (222244570758419 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-21724441770 / 1000000000000) (-21724441583 / 1000000000000), orderedInterval (105011884558 / 1000000000000) (105011884745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (596980178341943 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45317288515 / 1000000000000) (-45317238294 / 1000000000000), orderedInterval (47183136051 / 1000000000000) (47183186272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1620917313381531 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26987402065 / 1000000000000) (-26987402064 / 1000000000000), orderedInterval (-28995847094 / 1000000000000) (-28995847093 / 1000000000000)))) (orderedInterval (-8244741289 / 1000000000000) (-8244740860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1193960356684403 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33884365537 / 1000000000000) (-33884365536 / 1000000000000), orderedInterval (-31322372334 / 1000000000000) (-31322372333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2045871421581119 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6087202752 / 1000000000000) (-6087202751 / 1000000000000), orderedInterval (-34745138175 / 1000000000000) (-34745138174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1506979629420221 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21094233751 / 1000000000000) (21094233752 / 1000000000000), orderedInterval (35254068023 / 1000000000000) (35254068024 / 1000000000000)))) (orderedInterval (-10931626962 / 1000000000000) (-10931626879 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate387_chunkChecks3_1 :
    compactCertificate387.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2312094288734483 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22759687359 / 1000000000000) (22759687360 / 1000000000000), orderedInterval (24133366775 / 1000000000000) (24133366776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1334888259992507 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43561623760 / 1000000000000) (43561623824 / 1000000000000), orderedInterval (3099770459 / 1000000000000) (3099770523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2368782642407863 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23062539777 / 1000000000000) (23062546554 / 1000000000000), orderedInterval (-23324733129 / 1000000000000) (-23324726352 / 1000000000000)))) (orderedInterval (87323435014 / 1000000000000) (87323447626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2213224014940147 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31243451593 / 1000000000000) (31243451596 / 1000000000000), orderedInterval (13178616856 / 1000000000000) (13178616859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1579461089527651 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-7595837984 / 1000000000000) (-7595837972 / 1000000000000), orderedInterval (39437400080 / 1000000000000) (39437400093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1790940535025829 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25075657391 / 1000000000000) (25075665746 / 1000000000000), orderedInterval (-28189651075 / 1000000000000) (-28189642720 / 1000000000000)))) (orderedInterval (-11718053710 / 1000000000000) (-11718053344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1493099503167701 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8625599745 / 1000000000000) (-8625599744 / 1000000000000), orderedInterval (-40375312874 / 1000000000000) (-40375312873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1319198692213721 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28886463585 / 1000000000000) (-28886463584 / 1000000000000), orderedInterval (-33060513304 / 1000000000000) (-33060513303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (382355199242379 / 800000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34108600614 / 1000000000000) (34108600616 / 1000000000000), orderedInterval (12948900577 / 1000000000000) (12948900579 / 1000000000000)))) (orderedInterval (-4599407270 / 1000000000000) (-4599407187 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate387_chunkChecks3_2 :
    compactCertificate387.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1057614603356113 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47211717221 / 1000000000000) (47211717223 / 1000000000000), orderedInterval (13282601992 / 1000000000000) (13282601994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (896551612025993 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50931904919 / 1000000000000) (-50931901559 / 1000000000000), orderedInterval (15805630175 / 1000000000000) (15805633535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (561020370579779 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21963298985 / 1000000000000) (21963299555 / 1000000000000), orderedInterval (-63770131533 / 1000000000000) (-63770130963 / 1000000000000)))) (orderedInterval (3165935740 / 1000000000000) (3165935924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (301718621167293 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66865574220 / 1000000000000) (66865574221 / 1000000000000), orderedInterval (62555974933 / 1000000000000) (62555974934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (819224749100879 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54818510100 / 1000000000000) (-54818510095 / 1000000000000), orderedInterval (-10030981313 / 1000000000000) (-10030981309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1118581357219183 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35161943428 / 1000000000000) (-35161943427 / 1000000000000), orderedInterval (-32188689727 / 1000000000000) (-32188689726 / 1000000000000)))) (orderedInterval (-3192746375 / 1000000000000) (-3192746345 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (472979629420221 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25247738393 / 1000000000000) (-25247737569 / 1000000000000), orderedInterval (69001583997 / 1000000000000) (69001584821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1922635934549341 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25606187315 / 1000000000000) (-25606187314 / 1000000000000), orderedInterval (-25834454435 / 1000000000000) (-25834454434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1284231701516819 / 4000000000000) 3 (IntervalRat.scale (517 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43885266809 / 1000000000000) (43885266822 / 1000000000000), orderedInterval (7479001911 / 1000000000000) (7479001924 / 1000000000000)))) (orderedInterval (-10892210359 / 1000000000000) (-10892210124 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate387_chunkChecks3 :
    compactCertificate387.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate387.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate387_chunkChecks3_0
    compactCertificate387_chunkChecks3_1 compactCertificate387_chunkChecks3_2

theorem compactCertificate387_chunkChecks4_0 :
    compactCertificate387.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (517 / 2) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49360340388 / 1000000000000) (49360340804 / 1000000000000), orderedInterval (-5223632110 / 1000000000000) (-5223631694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (761639720064817 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (24758423610 / 1000000000000) (24758425186 / 1000000000000), orderedInterval (-52318670031 / 1000000000000) (-52318668456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (246298636593361 / 800000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32051532474 / 1000000000000) (32051532475 / 1000000000000), orderedInterval (32204686493 / 1000000000000) (32204686494 / 1000000000000)))) (orderedInterval (23423163885 / 1000000000000) (23423164088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (222244570758419 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-21724441770 / 1000000000000) (-21724441583 / 1000000000000), orderedInterval (105011884558 / 1000000000000) (105011884745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (596980178341943 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45317288515 / 1000000000000) (-45317238294 / 1000000000000), orderedInterval (47183136051 / 1000000000000) (47183186272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1620917313381531 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26987402065 / 1000000000000) (-26987402064 / 1000000000000), orderedInterval (-28995847094 / 1000000000000) (-28995847093 / 1000000000000)))) (orderedInterval (11466254247 / 1000000000000) (11466254567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1193960356684403 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33884365537 / 1000000000000) (-33884365536 / 1000000000000), orderedInterval (-31322372334 / 1000000000000) (-31322372333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2045871421581119 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6087202752 / 1000000000000) (-6087202751 / 1000000000000), orderedInterval (-34745138175 / 1000000000000) (-34745138174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1506979629420221 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21094233751 / 1000000000000) (21094233752 / 1000000000000), orderedInterval (35254068023 / 1000000000000) (35254068024 / 1000000000000)))) (orderedInterval (5262208105 / 1000000000000) (5262208257 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate387_chunkChecks4_1 :
    compactCertificate387.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2312094288734483 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22759687359 / 1000000000000) (22759687360 / 1000000000000), orderedInterval (24133366775 / 1000000000000) (24133366776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1334888259992507 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43561623760 / 1000000000000) (43561623824 / 1000000000000), orderedInterval (3099770459 / 1000000000000) (3099770523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2368782642407863 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23062539777 / 1000000000000) (23062546554 / 1000000000000), orderedInterval (-23324733129 / 1000000000000) (-23324726352 / 1000000000000)))) (orderedInterval (-2512642429 / 1000000000000) (-2512613572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2213224014940147 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31243451593 / 1000000000000) (31243451596 / 1000000000000), orderedInterval (13178616856 / 1000000000000) (13178616859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1579461089527651 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-7595837984 / 1000000000000) (-7595837972 / 1000000000000), orderedInterval (39437400080 / 1000000000000) (39437400093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1790940535025829 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25075657391 / 1000000000000) (25075665746 / 1000000000000), orderedInterval (-28189651075 / 1000000000000) (-28189642720 / 1000000000000)))) (orderedInterval (-16801406506 / 1000000000000) (-16801405873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1493099503167701 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8625599745 / 1000000000000) (-8625599744 / 1000000000000), orderedInterval (-40375312874 / 1000000000000) (-40375312873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1319198692213721 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28886463585 / 1000000000000) (-28886463584 / 1000000000000), orderedInterval (-33060513304 / 1000000000000) (-33060513303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (382355199242379 / 800000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34108600614 / 1000000000000) (34108600616 / 1000000000000), orderedInterval (12948900577 / 1000000000000) (12948900579 / 1000000000000)))) (orderedInterval (14187765248 / 1000000000000) (14187765379 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate387_chunkChecks4_2 :
    compactCertificate387.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1057614603356113 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47211717221 / 1000000000000) (47211717223 / 1000000000000), orderedInterval (13282601992 / 1000000000000) (13282601994 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (896551612025993 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50931904919 / 1000000000000) (-50931901559 / 1000000000000), orderedInterval (15805630175 / 1000000000000) (15805633535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (561020370579779 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21963298985 / 1000000000000) (21963299555 / 1000000000000), orderedInterval (-63770131533 / 1000000000000) (-63770130963 / 1000000000000)))) (orderedInterval (-6595439260 / 1000000000000) (-6595439094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (301718621167293 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66865574220 / 1000000000000) (66865574221 / 1000000000000), orderedInterval (62555974933 / 1000000000000) (62555974934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (819224749100879 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54818510100 / 1000000000000) (-54818510095 / 1000000000000), orderedInterval (-10030981313 / 1000000000000) (-10030981309 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1118581357219183 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35161943428 / 1000000000000) (-35161943427 / 1000000000000), orderedInterval (-32188689727 / 1000000000000) (-32188689726 / 1000000000000)))) (orderedInterval (4196445205 / 1000000000000) (4196445236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (472979629420221 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25247738393 / 1000000000000) (-25247737569 / 1000000000000), orderedInterval (69001583997 / 1000000000000) (69001584821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1922635934549341 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25606187315 / 1000000000000) (-25606187314 / 1000000000000), orderedInterval (-25834454435 / 1000000000000) (-25834454434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1284231701516819 / 4000000000000) 4 (IntervalRat.scale (517 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43885266809 / 1000000000000) (43885266822 / 1000000000000), orderedInterval (7479001911 / 1000000000000) (7479001924 / 1000000000000)))) (orderedInterval (5400911750 / 1000000000000) (5400912126 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate387_chunkChecks4 :
    compactCertificate387.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate387.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate387_chunkChecks4_0
    compactCertificate387_chunkChecks4_1 compactCertificate387_chunkChecks4_2

theorem compactCertificate387_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate387.chunkCheck r b = true :=
  compactCertificate387.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate387_chunkChecks0
    · exact compactCertificate387_chunkChecks1
    · exact compactCertificate387_chunkChecks2
    · exact compactCertificate387_chunkChecks3
    · exact compactCertificate387_chunkChecks4)

theorem compactCertificate387_coefficient0 :
    compactCertificate387.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate387_coefficient1 :
    compactCertificate387.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate387_coefficient2 :
    compactCertificate387.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate387_coefficient3 :
    compactCertificate387.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate387_coefficient4 :
    compactCertificate387.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate387_coefficients : ∀ r : Fin 5,
    compactCertificate387.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate387_coefficient0
  · exact compactCertificate387_coefficient1
  · exact compactCertificate387_coefficient2
  · exact compactCertificate387_coefficient3
  · exact compactCertificate387_coefficient4

theorem compactCertificate387_lower : (1 : ℚ) ≤ compactCertificate387.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate387, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate387_proves {t : ℝ} (ht : t ∈ compactCertificate387.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate387.proves compactCertificate387_states compactCertificate387_chunks
    compactCertificate387_coefficients compactCertificate387_lower ht

end Erdos232
