/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate302 : CompactCertificate where
  left := 175
  right := 176
  center := 351 / 2
  grid := fun i =>
    match i.val with
    | 0 => 56
    | 1 => 41
    | 2 => 67
    | 3 => 12
    | 4 => 32
    | 5 => 88
    | 6 => 65
    | 7 => 111
    | 8 => 81
    | 9 => 125
    | 10 => 72
    | 11 => 128
    | 12 => 120
    | 13 => 85
    | 14 => 97
    | 15 => 81
    | 16 => 71
    | 17 => 103
    | 18 => 57
    | 19 => 48
    | 20 => 30
    | 21 => 16
    | 22 => 44
    | 23 => 60
    | 24 => 26
    | 25 => 104
    | _ => 69
  point := fun i =>
    match i.val with
    | 0 => 351 / 2
    | 1 => 517090022713251 / 4000000000000
    | 2 => 167216289060483 / 800000000000
    | 3 => 150885578986857 / 4000000000000
    | 4 => 405299888971029 / 4000000000000
    | 5 => 1100468040612993 / 4000000000000
    | 6 => 810599777942409 / 4000000000000
    | 7 => 1388976535734957 / 4000000000000
    | 8 => 1023113829645063 / 4000000000000
    | 9 => 1569719720204649 / 4000000000000
    | 10 => 906278103012321 / 4000000000000
    | 11 => 1608206397456789 / 4000000000000
    | 12 => 1502595027551241 / 4000000000000
    | 13 => 1072322712619353 / 4000000000000
    | 14 => 1215899666913087 / 4000000000000
    | 15 => 1013690378359503 / 4000000000000
    | 16 => 895626191425563 / 4000000000000
    | 17 => 259587378982737 / 800000000000
    | 18 => 718032351601539 / 4000000000000
    | 19 => 608683976443179 / 4000000000000
    | 20 => 380886170354937 / 4000000000000
    | 21 => 204841849187079 / 4000000000000
    | 22 => 556185467958237 / 4000000000000
    | 23 => 759423706738749 / 4000000000000
    | 24 => 321113829645063 / 4000000000000
    | 25 => 1305309889800423 / 4000000000000
    | _ => 871886513022057 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (20962860211 / 1000000000000) (20962860212 / 1000000000000), orderedInterval (56402943985 / 1000000000000) (56402943986 / 1000000000000))
    | 1 => (orderedInterval (-66631604259 / 1000000000000) (-66631604258 / 1000000000000), orderedInterval (-21761225820 / 1000000000000) (-21761225819 / 1000000000000))
    | 2 => (orderedInterval (34768174657 / 1000000000000) (34768192086 / 1000000000000), orderedInterval (-42942319775 / 1000000000000) (-42942302346 / 1000000000000))
    | 3 => (orderedInterval (93582900722 / 1000000000000) (93582900723 / 1000000000000), orderedInterval (88865668021 / 1000000000000) (88865668022 / 1000000000000))
    | 4 => (orderedInterval (79262425600 / 1000000000000) (79262425637 / 1000000000000), orderedInterval (-975743758 / 1000000000000) (-975743721 / 1000000000000))
    | 5 => (orderedInterval (-25478749042 / 1000000000000) (-25478745492 / 1000000000000), orderedInterval (40848650261 / 1000000000000) (40848653812 / 1000000000000))
    | 6 => (orderedInterval (38969060589 / 1000000000000) (38969100838 / 1000000000000), orderedInterval (-40381229180 / 1000000000000) (-40381188931 / 1000000000000))
    | 7 => (orderedInterval (27176070968 / 1000000000000) (27176080303 / 1000000000000), orderedInterval (-33127056664 / 1000000000000) (-33127047329 / 1000000000000))
    | 8 => (orderedInterval (-43206271329 / 1000000000000) (-43206235070 / 1000000000000), orderedInterval (25027720395 / 1000000000000) (25027756654 / 1000000000000))
    | 9 => (orderedInterval (-19870424333 / 1000000000000) (-19870424332 / 1000000000000), orderedInterval (-35009204766 / 1000000000000) (-35009204765 / 1000000000000))
    | 10 => (orderedInterval (48591276382 / 1000000000000) (48591276383 / 1000000000000), orderedInterval (21075403044 / 1000000000000) (21075403045 / 1000000000000))
    | 11 => (orderedInterval (26023167655 / 1000000000000) (26023167656 / 1000000000000), orderedInterval (30071174302 / 1000000000000) (30071174303 / 1000000000000))
    | 12 => (orderedInterval (-21772938959 / 1000000000000) (-21772936953 / 1000000000000), orderedInterval (34966933816 / 1000000000000) (34966935822 / 1000000000000))
    | 13 => (orderedInterval (-47100356429 / 1000000000000) (-47100353645 / 1000000000000), orderedInterval (12589245193 / 1000000000000) (12589247977 / 1000000000000))
    | 14 => (orderedInterval (-1163017048 / 1000000000000) (-1163017046 / 1000000000000), orderedInterval (-45747043401 / 1000000000000) (-45747043399 / 1000000000000))
    | 15 => (orderedInterval (12957955153 / 1000000000000) (12957955258 / 1000000000000), orderedInterval (-48442332491 / 1000000000000) (-48442332385 / 1000000000000))
    | 16 => (orderedInterval (-53200487511 / 1000000000000) (-53200487303 / 1000000000000), orderedInterval (3716001779 / 1000000000000) (3716001986 / 1000000000000))
    | 17 => (orderedInterval (-44004294036 / 1000000000000) (-44004293313 / 1000000000000), orderedInterval (5123846910 / 1000000000000) (5123847633 / 1000000000000))
    | 18 => (orderedInterval (-55966345495 / 1000000000000) (-55966345494 / 1000000000000), orderedInterval (-20196658184 / 1000000000000) (-20196658183 / 1000000000000))
    | 19 => (orderedInterval (53805709143 / 1000000000000) (53805749732 / 1000000000000), orderedInterval (-36072720618 / 1000000000000) (-36072680028 / 1000000000000))
    | 20 => (orderedInterval (80339121592 / 1000000000000) (80339122016 / 1000000000000), orderedInterval (-15627411195 / 1000000000000) (-15627410770 / 1000000000000))
    | 21 => (orderedInterval (110119962983 / 1000000000000) (110119963201 / 1000000000000), orderedInterval (-18524144057 / 1000000000000) (-18524143839 / 1000000000000))
    | 22 => (orderedInterval (67633749140 / 1000000000000) (67633749208 / 1000000000000), orderedInterval (-2272370845 / 1000000000000) (-2272370777 / 1000000000000))
    | 23 => (orderedInterval (48616345911 / 1000000000000) (48616388331 / 1000000000000), orderedInterval (-31586233376 / 1000000000000) (-31586190956 / 1000000000000))
    | 24 => (orderedInterval (-51676980057 / 1000000000000) (-51676962308 / 1000000000000), orderedInterval (72845527131 / 1000000000000) (72845544880 / 1000000000000))
    | 25 => (orderedInterval (16663663639 / 1000000000000) (16663663640 / 1000000000000), orderedInterval (40879060184 / 1000000000000) (40879060185 / 1000000000000))
    | _ => (orderedInterval (-49438991563 / 1000000000000) (-49438980640 / 1000000000000), orderedInterval (21940808924 / 1000000000000) (21940819847 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9728302773 / 1000000000000) (9728303809 / 1000000000000)
      | 1 => orderedInterval (3689976288 / 1000000000000) (3689976563 / 1000000000000)
      | 2 => orderedInterval (-1882429385 / 1000000000000) (-1882428211 / 1000000000000)
      | 3 => orderedInterval (10830294786 / 1000000000000) (10830294857 / 1000000000000)
      | 4 => orderedInterval (-4054990465 / 1000000000000) (-4054990144 / 1000000000000)
      | 5 => orderedInterval (2067437540 / 1000000000000) (2067437589 / 1000000000000)
      | 6 => orderedInterval (8518654436 / 1000000000000) (8518656792 / 1000000000000)
      | 7 => orderedInterval (-7293680615 / 1000000000000) (-7293677337 / 1000000000000)
      | _ => orderedInterval (7608086594 / 1000000000000) (7608088800 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19205587248 / 1000000000000) (19205588481 / 1000000000000)
      | 1 => orderedInterval (-4780027638 / 1000000000000) (-4780027217 / 1000000000000)
      | 2 => orderedInterval (2903229335 / 1000000000000) (2903231200 / 1000000000000)
      | 3 => orderedInterval (25718936920 / 1000000000000) (25718937066 / 1000000000000)
      | 4 => orderedInterval (868279539 / 1000000000000) (868280053 / 1000000000000)
      | 5 => orderedInterval (-836518572 / 1000000000000) (-836518496 / 1000000000000)
      | 6 => orderedInterval (4797317205 / 1000000000000) (4797319246 / 1000000000000)
      | 7 => orderedInterval (2759400273 / 1000000000000) (2759403812 / 1000000000000)
      | _ => orderedInterval (-11099502406 / 1000000000000) (-11099499743 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-10975540106 / 1000000000000) (-10975538631 / 1000000000000)
      | 1 => orderedInterval (-5341604835 / 1000000000000) (-5341604178 / 1000000000000)
      | 2 => orderedInterval (5482960407 / 1000000000000) (5482963438 / 1000000000000)
      | 3 => orderedInterval (-43215440272 / 1000000000000) (-43215439961 / 1000000000000)
      | 4 => orderedInterval (8569080264 / 1000000000000) (8569081104 / 1000000000000)
      | 5 => orderedInterval (-1411266384 / 1000000000000) (-1411266261 / 1000000000000)
      | 6 => orderedInterval (-7869719635 / 1000000000000) (-7869717853 / 1000000000000)
      | 7 => orderedInterval (5480971926 / 1000000000000) (5480975771 / 1000000000000)
      | _ => orderedInterval (-9490746608 / 1000000000000) (-9490743308 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-17954807433 / 1000000000000) (-17954805677 / 1000000000000)
      | 1 => orderedInterval (11233488409 / 1000000000000) (11233489436 / 1000000000000)
      | 2 => orderedInterval (-9818218767 / 1000000000000) (-9818213751 / 1000000000000)
      | 3 => orderedInterval (-124058446393 / 1000000000000) (-124058445711 / 1000000000000)
      | 4 => orderedInterval (695604622 / 1000000000000) (695606016 / 1000000000000)
      | 5 => orderedInterval (1304759515 / 1000000000000) (1304759717 / 1000000000000)
      | 6 => orderedInterval (-4660321171 / 1000000000000) (-4660319623 / 1000000000000)
      | 7 => orderedInterval (-3129978970 / 1000000000000) (-3129974811 / 1000000000000)
      | _ => orderedInterval (29291389992 / 1000000000000) (29291394103 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12435544466 / 1000000000000) (12435546566 / 1000000000000)
      | 1 => orderedInterval (11129394891 / 1000000000000) (11129396503 / 1000000000000)
      | 2 => orderedInterval (-17445790646 / 1000000000000) (-17445782121 / 1000000000000)
      | 3 => orderedInterval (201574170564 / 1000000000000) (201574172076 / 1000000000000)
      | 4 => orderedInterval (-15953290572 / 1000000000000) (-15953288198 / 1000000000000)
      | 5 => orderedInterval (-4464484522 / 1000000000000) (-4464484178 / 1000000000000)
      | 6 => orderedInterval (8352691847 / 1000000000000) (8352693202 / 1000000000000)
      | 7 => orderedInterval (-5686428564 / 1000000000000) (-5686424043 / 1000000000000)
      | _ => orderedInterval (5510176456 / 1000000000000) (5510181634 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (29211651952 / 1000000000000) (29211662718 / 1000000000000)
    | 1 => orderedInterval (39536701904 / 1000000000000) (39536714402 / 1000000000000)
    | 2 => orderedInterval (-58771305243 / 1000000000000) (-58771289879 / 1000000000000)
    | 3 => orderedInterval (-117096530196 / 1000000000000) (-117096510301 / 1000000000000)
    | _ => orderedInterval (195451983920 / 1000000000000) (195452011441 / 1000000000000)

theorem compactCertificate302_stateChecks0 :
    compactCertificate302.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (351 / 2)) (orderedInterval (20962860211 / 1000000000000) (20962860212 / 1000000000000), orderedInterval (56402943985 / 1000000000000) (56402943986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (517090022713251 / 4000000000000)) (orderedInterval (-66631604259 / 1000000000000) (-66631604258 / 1000000000000), orderedInterval (-21761225820 / 1000000000000) (-21761225819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (167216289060483 / 800000000000)) (orderedInterval (34768174657 / 1000000000000) (34768192086 / 1000000000000), orderedInterval (-42942319775 / 1000000000000) (-42942302346 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_stateChecks1 :
    compactCertificate302.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (150885578986857 / 4000000000000)) (orderedInterval (93582900722 / 1000000000000) (93582900723 / 1000000000000), orderedInterval (88865668021 / 1000000000000) (88865668022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (405299888971029 / 4000000000000)) (orderedInterval (79262425600 / 1000000000000) (79262425637 / 1000000000000), orderedInterval (-975743758 / 1000000000000) (-975743721 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1100468040612993 / 4000000000000)) (orderedInterval (-25478749042 / 1000000000000) (-25478745492 / 1000000000000), orderedInterval (40848650261 / 1000000000000) (40848653812 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_stateChecks2 :
    compactCertificate302.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (810599777942409 / 4000000000000)) (orderedInterval (38969060589 / 1000000000000) (38969100838 / 1000000000000), orderedInterval (-40381229180 / 1000000000000) (-40381188931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1388976535734957 / 4000000000000)) (orderedInterval (27176070968 / 1000000000000) (27176080303 / 1000000000000), orderedInterval (-33127056664 / 1000000000000) (-33127047329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1023113829645063 / 4000000000000)) (orderedInterval (-43206271329 / 1000000000000) (-43206235070 / 1000000000000), orderedInterval (25027720395 / 1000000000000) (25027756654 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_stateChecks3 :
    compactCertificate302.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1569719720204649 / 4000000000000)) (orderedInterval (-19870424333 / 1000000000000) (-19870424332 / 1000000000000), orderedInterval (-35009204766 / 1000000000000) (-35009204765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (906278103012321 / 4000000000000)) (orderedInterval (48591276382 / 1000000000000) (48591276383 / 1000000000000), orderedInterval (21075403044 / 1000000000000) (21075403045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1608206397456789 / 4000000000000)) (orderedInterval (26023167655 / 1000000000000) (26023167656 / 1000000000000), orderedInterval (30071174302 / 1000000000000) (30071174303 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_stateChecks4 :
    compactCertificate302.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1502595027551241 / 4000000000000)) (orderedInterval (-21772938959 / 1000000000000) (-21772936953 / 1000000000000), orderedInterval (34966933816 / 1000000000000) (34966935822 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1072322712619353 / 4000000000000)) (orderedInterval (-47100356429 / 1000000000000) (-47100353645 / 1000000000000), orderedInterval (12589245193 / 1000000000000) (12589247977 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1215899666913087 / 4000000000000)) (orderedInterval (-1163017048 / 1000000000000) (-1163017046 / 1000000000000), orderedInterval (-45747043401 / 1000000000000) (-45747043399 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_stateChecks5 :
    compactCertificate302.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1013690378359503 / 4000000000000)) (orderedInterval (12957955153 / 1000000000000) (12957955258 / 1000000000000), orderedInterval (-48442332491 / 1000000000000) (-48442332385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (895626191425563 / 4000000000000)) (orderedInterval (-53200487511 / 1000000000000) (-53200487303 / 1000000000000), orderedInterval (3716001779 / 1000000000000) (3716001986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (259587378982737 / 800000000000)) (orderedInterval (-44004294036 / 1000000000000) (-44004293313 / 1000000000000), orderedInterval (5123846910 / 1000000000000) (5123847633 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_stateChecks6 :
    compactCertificate302.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (718032351601539 / 4000000000000)) (orderedInterval (-55966345495 / 1000000000000) (-55966345494 / 1000000000000), orderedInterval (-20196658184 / 1000000000000) (-20196658183 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (608683976443179 / 4000000000000)) (orderedInterval (53805709143 / 1000000000000) (53805749732 / 1000000000000), orderedInterval (-36072720618 / 1000000000000) (-36072680028 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (380886170354937 / 4000000000000)) (orderedInterval (80339121592 / 1000000000000) (80339122016 / 1000000000000), orderedInterval (-15627411195 / 1000000000000) (-15627410770 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_stateChecks7 :
    compactCertificate302.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (204841849187079 / 4000000000000)) (orderedInterval (110119962983 / 1000000000000) (110119963201 / 1000000000000), orderedInterval (-18524144057 / 1000000000000) (-18524143839 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (556185467958237 / 4000000000000)) (orderedInterval (67633749140 / 1000000000000) (67633749208 / 1000000000000), orderedInterval (-2272370845 / 1000000000000) (-2272370777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (759423706738749 / 4000000000000)) (orderedInterval (48616345911 / 1000000000000) (48616388331 / 1000000000000), orderedInterval (-31586233376 / 1000000000000) (-31586190956 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_stateChecks8 :
    compactCertificate302.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (321113829645063 / 4000000000000)) (orderedInterval (-51676980057 / 1000000000000) (-51676962308 / 1000000000000), orderedInterval (72845527131 / 1000000000000) (72845544880 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1305309889800423 / 4000000000000)) (orderedInterval (16663663639 / 1000000000000) (16663663640 / 1000000000000), orderedInterval (40879060184 / 1000000000000) (40879060185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (871886513022057 / 4000000000000)) (orderedInterval (-49438991563 / 1000000000000) (-49438980640 / 1000000000000), orderedInterval (21940808924 / 1000000000000) (21940819847 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_states : ∀ j,
    BesselStateValid (compactCertificate302.point j) (compactCertificate302.state j) :=
  compactCertificate302.statesValid_of_checks3 compactCertificate302_stateChecks0
    compactCertificate302_stateChecks1 compactCertificate302_stateChecks2
    compactCertificate302_stateChecks3 compactCertificate302_stateChecks4
    compactCertificate302_stateChecks5 compactCertificate302_stateChecks6
    compactCertificate302_stateChecks7 compactCertificate302_stateChecks8

theorem compactCertificate302_chunkChecks0_0 :
    compactCertificate302.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (351 / 2) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20962860211 / 1000000000000) (20962860212 / 1000000000000), orderedInterval (56402943985 / 1000000000000) (56402943986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (517090022713251 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66631604259 / 1000000000000) (-66631604258 / 1000000000000), orderedInterval (-21761225820 / 1000000000000) (-21761225819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (167216289060483 / 800000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34768174657 / 1000000000000) (34768192086 / 1000000000000), orderedInterval (-42942319775 / 1000000000000) (-42942302346 / 1000000000000)))) (orderedInterval (9728302773 / 1000000000000) (9728303809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (150885578986857 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93582900722 / 1000000000000) (93582900723 / 1000000000000), orderedInterval (88865668021 / 1000000000000) (88865668022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (405299888971029 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (79262425600 / 1000000000000) (79262425637 / 1000000000000), orderedInterval (-975743758 / 1000000000000) (-975743721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1100468040612993 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25478749042 / 1000000000000) (-25478745492 / 1000000000000), orderedInterval (40848650261 / 1000000000000) (40848653812 / 1000000000000)))) (orderedInterval (3689976288 / 1000000000000) (3689976563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (810599777942409 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38969060589 / 1000000000000) (38969100838 / 1000000000000), orderedInterval (-40381229180 / 1000000000000) (-40381188931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1388976535734957 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27176070968 / 1000000000000) (27176080303 / 1000000000000), orderedInterval (-33127056664 / 1000000000000) (-33127047329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1023113829645063 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43206271329 / 1000000000000) (-43206235070 / 1000000000000), orderedInterval (25027720395 / 1000000000000) (25027756654 / 1000000000000)))) (orderedInterval (-1882429385 / 1000000000000) (-1882428211 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks0_1 :
    compactCertificate302.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1569719720204649 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19870424333 / 1000000000000) (-19870424332 / 1000000000000), orderedInterval (-35009204766 / 1000000000000) (-35009204765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (906278103012321 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48591276382 / 1000000000000) (48591276383 / 1000000000000), orderedInterval (21075403044 / 1000000000000) (21075403045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1608206397456789 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26023167655 / 1000000000000) (26023167656 / 1000000000000), orderedInterval (30071174302 / 1000000000000) (30071174303 / 1000000000000)))) (orderedInterval (10830294786 / 1000000000000) (10830294857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1502595027551241 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21772938959 / 1000000000000) (-21772936953 / 1000000000000), orderedInterval (34966933816 / 1000000000000) (34966935822 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1072322712619353 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47100356429 / 1000000000000) (-47100353645 / 1000000000000), orderedInterval (12589245193 / 1000000000000) (12589247977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1215899666913087 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1163017048 / 1000000000000) (-1163017046 / 1000000000000), orderedInterval (-45747043401 / 1000000000000) (-45747043399 / 1000000000000)))) (orderedInterval (-4054990465 / 1000000000000) (-4054990144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1013690378359503 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12957955153 / 1000000000000) (12957955258 / 1000000000000), orderedInterval (-48442332491 / 1000000000000) (-48442332385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (895626191425563 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53200487511 / 1000000000000) (-53200487303 / 1000000000000), orderedInterval (3716001779 / 1000000000000) (3716001986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (259587378982737 / 800000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-44004294036 / 1000000000000) (-44004293313 / 1000000000000), orderedInterval (5123846910 / 1000000000000) (5123847633 / 1000000000000)))) (orderedInterval (2067437540 / 1000000000000) (2067437589 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks0_2 :
    compactCertificate302.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (718032351601539 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55966345495 / 1000000000000) (-55966345494 / 1000000000000), orderedInterval (-20196658184 / 1000000000000) (-20196658183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (608683976443179 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53805709143 / 1000000000000) (53805749732 / 1000000000000), orderedInterval (-36072720618 / 1000000000000) (-36072680028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (380886170354937 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80339121592 / 1000000000000) (80339122016 / 1000000000000), orderedInterval (-15627411195 / 1000000000000) (-15627410770 / 1000000000000)))) (orderedInterval (8518654436 / 1000000000000) (8518656792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (204841849187079 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110119962983 / 1000000000000) (110119963201 / 1000000000000), orderedInterval (-18524144057 / 1000000000000) (-18524143839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (556185467958237 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (67633749140 / 1000000000000) (67633749208 / 1000000000000), orderedInterval (-2272370845 / 1000000000000) (-2272370777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (759423706738749 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48616345911 / 1000000000000) (48616388331 / 1000000000000), orderedInterval (-31586233376 / 1000000000000) (-31586190956 / 1000000000000)))) (orderedInterval (-7293680615 / 1000000000000) (-7293677337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (321113829645063 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51676980057 / 1000000000000) (-51676962308 / 1000000000000), orderedInterval (72845527131 / 1000000000000) (72845544880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1305309889800423 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16663663639 / 1000000000000) (16663663640 / 1000000000000), orderedInterval (40879060184 / 1000000000000) (40879060185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (871886513022057 / 4000000000000) 0 (IntervalRat.scale (351 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49438991563 / 1000000000000) (-49438980640 / 1000000000000), orderedInterval (21940808924 / 1000000000000) (21940819847 / 1000000000000)))) (orderedInterval (7608086594 / 1000000000000) (7608088800 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks0 :
    compactCertificate302.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate302.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate302_chunkChecks0_0
    compactCertificate302_chunkChecks0_1 compactCertificate302_chunkChecks0_2

theorem compactCertificate302_chunkChecks1_0 :
    compactCertificate302.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (351 / 2) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20962860211 / 1000000000000) (20962860212 / 1000000000000), orderedInterval (56402943985 / 1000000000000) (56402943986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (517090022713251 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66631604259 / 1000000000000) (-66631604258 / 1000000000000), orderedInterval (-21761225820 / 1000000000000) (-21761225819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (167216289060483 / 800000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34768174657 / 1000000000000) (34768192086 / 1000000000000), orderedInterval (-42942319775 / 1000000000000) (-42942302346 / 1000000000000)))) (orderedInterval (19205587248 / 1000000000000) (19205588481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (150885578986857 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93582900722 / 1000000000000) (93582900723 / 1000000000000), orderedInterval (88865668021 / 1000000000000) (88865668022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (405299888971029 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (79262425600 / 1000000000000) (79262425637 / 1000000000000), orderedInterval (-975743758 / 1000000000000) (-975743721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1100468040612993 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25478749042 / 1000000000000) (-25478745492 / 1000000000000), orderedInterval (40848650261 / 1000000000000) (40848653812 / 1000000000000)))) (orderedInterval (-4780027638 / 1000000000000) (-4780027217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (810599777942409 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38969060589 / 1000000000000) (38969100838 / 1000000000000), orderedInterval (-40381229180 / 1000000000000) (-40381188931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1388976535734957 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27176070968 / 1000000000000) (27176080303 / 1000000000000), orderedInterval (-33127056664 / 1000000000000) (-33127047329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1023113829645063 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43206271329 / 1000000000000) (-43206235070 / 1000000000000), orderedInterval (25027720395 / 1000000000000) (25027756654 / 1000000000000)))) (orderedInterval (2903229335 / 1000000000000) (2903231200 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks1_1 :
    compactCertificate302.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1569719720204649 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19870424333 / 1000000000000) (-19870424332 / 1000000000000), orderedInterval (-35009204766 / 1000000000000) (-35009204765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (906278103012321 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48591276382 / 1000000000000) (48591276383 / 1000000000000), orderedInterval (21075403044 / 1000000000000) (21075403045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1608206397456789 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26023167655 / 1000000000000) (26023167656 / 1000000000000), orderedInterval (30071174302 / 1000000000000) (30071174303 / 1000000000000)))) (orderedInterval (25718936920 / 1000000000000) (25718937066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1502595027551241 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21772938959 / 1000000000000) (-21772936953 / 1000000000000), orderedInterval (34966933816 / 1000000000000) (34966935822 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1072322712619353 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47100356429 / 1000000000000) (-47100353645 / 1000000000000), orderedInterval (12589245193 / 1000000000000) (12589247977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1215899666913087 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1163017048 / 1000000000000) (-1163017046 / 1000000000000), orderedInterval (-45747043401 / 1000000000000) (-45747043399 / 1000000000000)))) (orderedInterval (868279539 / 1000000000000) (868280053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1013690378359503 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12957955153 / 1000000000000) (12957955258 / 1000000000000), orderedInterval (-48442332491 / 1000000000000) (-48442332385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (895626191425563 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53200487511 / 1000000000000) (-53200487303 / 1000000000000), orderedInterval (3716001779 / 1000000000000) (3716001986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (259587378982737 / 800000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-44004294036 / 1000000000000) (-44004293313 / 1000000000000), orderedInterval (5123846910 / 1000000000000) (5123847633 / 1000000000000)))) (orderedInterval (-836518572 / 1000000000000) (-836518496 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks1_2 :
    compactCertificate302.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (718032351601539 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55966345495 / 1000000000000) (-55966345494 / 1000000000000), orderedInterval (-20196658184 / 1000000000000) (-20196658183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (608683976443179 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53805709143 / 1000000000000) (53805749732 / 1000000000000), orderedInterval (-36072720618 / 1000000000000) (-36072680028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (380886170354937 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80339121592 / 1000000000000) (80339122016 / 1000000000000), orderedInterval (-15627411195 / 1000000000000) (-15627410770 / 1000000000000)))) (orderedInterval (4797317205 / 1000000000000) (4797319246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (204841849187079 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110119962983 / 1000000000000) (110119963201 / 1000000000000), orderedInterval (-18524144057 / 1000000000000) (-18524143839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (556185467958237 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (67633749140 / 1000000000000) (67633749208 / 1000000000000), orderedInterval (-2272370845 / 1000000000000) (-2272370777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (759423706738749 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48616345911 / 1000000000000) (48616388331 / 1000000000000), orderedInterval (-31586233376 / 1000000000000) (-31586190956 / 1000000000000)))) (orderedInterval (2759400273 / 1000000000000) (2759403812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (321113829645063 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51676980057 / 1000000000000) (-51676962308 / 1000000000000), orderedInterval (72845527131 / 1000000000000) (72845544880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1305309889800423 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16663663639 / 1000000000000) (16663663640 / 1000000000000), orderedInterval (40879060184 / 1000000000000) (40879060185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (871886513022057 / 4000000000000) 1 (IntervalRat.scale (351 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49438991563 / 1000000000000) (-49438980640 / 1000000000000), orderedInterval (21940808924 / 1000000000000) (21940819847 / 1000000000000)))) (orderedInterval (-11099502406 / 1000000000000) (-11099499743 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks1 :
    compactCertificate302.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate302.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate302_chunkChecks1_0
    compactCertificate302_chunkChecks1_1 compactCertificate302_chunkChecks1_2

theorem compactCertificate302_chunkChecks2_0 :
    compactCertificate302.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (351 / 2) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20962860211 / 1000000000000) (20962860212 / 1000000000000), orderedInterval (56402943985 / 1000000000000) (56402943986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (517090022713251 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66631604259 / 1000000000000) (-66631604258 / 1000000000000), orderedInterval (-21761225820 / 1000000000000) (-21761225819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (167216289060483 / 800000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34768174657 / 1000000000000) (34768192086 / 1000000000000), orderedInterval (-42942319775 / 1000000000000) (-42942302346 / 1000000000000)))) (orderedInterval (-10975540106 / 1000000000000) (-10975538631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (150885578986857 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93582900722 / 1000000000000) (93582900723 / 1000000000000), orderedInterval (88865668021 / 1000000000000) (88865668022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (405299888971029 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (79262425600 / 1000000000000) (79262425637 / 1000000000000), orderedInterval (-975743758 / 1000000000000) (-975743721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1100468040612993 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25478749042 / 1000000000000) (-25478745492 / 1000000000000), orderedInterval (40848650261 / 1000000000000) (40848653812 / 1000000000000)))) (orderedInterval (-5341604835 / 1000000000000) (-5341604178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (810599777942409 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38969060589 / 1000000000000) (38969100838 / 1000000000000), orderedInterval (-40381229180 / 1000000000000) (-40381188931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1388976535734957 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27176070968 / 1000000000000) (27176080303 / 1000000000000), orderedInterval (-33127056664 / 1000000000000) (-33127047329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1023113829645063 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43206271329 / 1000000000000) (-43206235070 / 1000000000000), orderedInterval (25027720395 / 1000000000000) (25027756654 / 1000000000000)))) (orderedInterval (5482960407 / 1000000000000) (5482963438 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks2_1 :
    compactCertificate302.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1569719720204649 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19870424333 / 1000000000000) (-19870424332 / 1000000000000), orderedInterval (-35009204766 / 1000000000000) (-35009204765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (906278103012321 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48591276382 / 1000000000000) (48591276383 / 1000000000000), orderedInterval (21075403044 / 1000000000000) (21075403045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1608206397456789 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26023167655 / 1000000000000) (26023167656 / 1000000000000), orderedInterval (30071174302 / 1000000000000) (30071174303 / 1000000000000)))) (orderedInterval (-43215440272 / 1000000000000) (-43215439961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1502595027551241 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21772938959 / 1000000000000) (-21772936953 / 1000000000000), orderedInterval (34966933816 / 1000000000000) (34966935822 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1072322712619353 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47100356429 / 1000000000000) (-47100353645 / 1000000000000), orderedInterval (12589245193 / 1000000000000) (12589247977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1215899666913087 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1163017048 / 1000000000000) (-1163017046 / 1000000000000), orderedInterval (-45747043401 / 1000000000000) (-45747043399 / 1000000000000)))) (orderedInterval (8569080264 / 1000000000000) (8569081104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1013690378359503 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12957955153 / 1000000000000) (12957955258 / 1000000000000), orderedInterval (-48442332491 / 1000000000000) (-48442332385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (895626191425563 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53200487511 / 1000000000000) (-53200487303 / 1000000000000), orderedInterval (3716001779 / 1000000000000) (3716001986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (259587378982737 / 800000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-44004294036 / 1000000000000) (-44004293313 / 1000000000000), orderedInterval (5123846910 / 1000000000000) (5123847633 / 1000000000000)))) (orderedInterval (-1411266384 / 1000000000000) (-1411266261 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks2_2 :
    compactCertificate302.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (718032351601539 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55966345495 / 1000000000000) (-55966345494 / 1000000000000), orderedInterval (-20196658184 / 1000000000000) (-20196658183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (608683976443179 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53805709143 / 1000000000000) (53805749732 / 1000000000000), orderedInterval (-36072720618 / 1000000000000) (-36072680028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (380886170354937 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80339121592 / 1000000000000) (80339122016 / 1000000000000), orderedInterval (-15627411195 / 1000000000000) (-15627410770 / 1000000000000)))) (orderedInterval (-7869719635 / 1000000000000) (-7869717853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (204841849187079 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110119962983 / 1000000000000) (110119963201 / 1000000000000), orderedInterval (-18524144057 / 1000000000000) (-18524143839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (556185467958237 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (67633749140 / 1000000000000) (67633749208 / 1000000000000), orderedInterval (-2272370845 / 1000000000000) (-2272370777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (759423706738749 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48616345911 / 1000000000000) (48616388331 / 1000000000000), orderedInterval (-31586233376 / 1000000000000) (-31586190956 / 1000000000000)))) (orderedInterval (5480971926 / 1000000000000) (5480975771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (321113829645063 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51676980057 / 1000000000000) (-51676962308 / 1000000000000), orderedInterval (72845527131 / 1000000000000) (72845544880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1305309889800423 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16663663639 / 1000000000000) (16663663640 / 1000000000000), orderedInterval (40879060184 / 1000000000000) (40879060185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (871886513022057 / 4000000000000) 2 (IntervalRat.scale (351 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49438991563 / 1000000000000) (-49438980640 / 1000000000000), orderedInterval (21940808924 / 1000000000000) (21940819847 / 1000000000000)))) (orderedInterval (-9490746608 / 1000000000000) (-9490743308 / 1000000000000))) = true
  rfl'

theorem compactCertificate302_chunkChecks2 :
    compactCertificate302.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate302.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate302_chunkChecks2_0
    compactCertificate302_chunkChecks2_1 compactCertificate302_chunkChecks2_2

theorem compactCertificate302_chunkChecks3_0 :
    compactCertificate302.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (351 / 2) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20962860211 / 1000000000000) (20962860212 / 1000000000000), orderedInterval (56402943985 / 1000000000000) (56402943986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (517090022713251 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66631604259 / 1000000000000) (-66631604258 / 1000000000000), orderedInterval (-21761225820 / 1000000000000) (-21761225819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (167216289060483 / 800000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34768174657 / 1000000000000) (34768192086 / 1000000000000), orderedInterval (-42942319775 / 1000000000000) (-42942302346 / 1000000000000)))) (orderedInterval (-17954807433 / 1000000000000) (-17954805677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (150885578986857 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93582900722 / 1000000000000) (93582900723 / 1000000000000), orderedInterval (88865668021 / 1000000000000) (88865668022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (405299888971029 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (79262425600 / 1000000000000) (79262425637 / 1000000000000), orderedInterval (-975743758 / 1000000000000) (-975743721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1100468040612993 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25478749042 / 1000000000000) (-25478745492 / 1000000000000), orderedInterval (40848650261 / 1000000000000) (40848653812 / 1000000000000)))) (orderedInterval (11233488409 / 1000000000000) (11233489436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (810599777942409 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38969060589 / 1000000000000) (38969100838 / 1000000000000), orderedInterval (-40381229180 / 1000000000000) (-40381188931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1388976535734957 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27176070968 / 1000000000000) (27176080303 / 1000000000000), orderedInterval (-33127056664 / 1000000000000) (-33127047329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1023113829645063 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43206271329 / 1000000000000) (-43206235070 / 1000000000000), orderedInterval (25027720395 / 1000000000000) (25027756654 / 1000000000000)))) (orderedInterval (-9818218767 / 1000000000000) (-9818213751 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate302_chunkChecks3_1 :
    compactCertificate302.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1569719720204649 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19870424333 / 1000000000000) (-19870424332 / 1000000000000), orderedInterval (-35009204766 / 1000000000000) (-35009204765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (906278103012321 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48591276382 / 1000000000000) (48591276383 / 1000000000000), orderedInterval (21075403044 / 1000000000000) (21075403045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1608206397456789 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26023167655 / 1000000000000) (26023167656 / 1000000000000), orderedInterval (30071174302 / 1000000000000) (30071174303 / 1000000000000)))) (orderedInterval (-124058446393 / 1000000000000) (-124058445711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1502595027551241 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21772938959 / 1000000000000) (-21772936953 / 1000000000000), orderedInterval (34966933816 / 1000000000000) (34966935822 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1072322712619353 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47100356429 / 1000000000000) (-47100353645 / 1000000000000), orderedInterval (12589245193 / 1000000000000) (12589247977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1215899666913087 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1163017048 / 1000000000000) (-1163017046 / 1000000000000), orderedInterval (-45747043401 / 1000000000000) (-45747043399 / 1000000000000)))) (orderedInterval (695604622 / 1000000000000) (695606016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1013690378359503 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12957955153 / 1000000000000) (12957955258 / 1000000000000), orderedInterval (-48442332491 / 1000000000000) (-48442332385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (895626191425563 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53200487511 / 1000000000000) (-53200487303 / 1000000000000), orderedInterval (3716001779 / 1000000000000) (3716001986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (259587378982737 / 800000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-44004294036 / 1000000000000) (-44004293313 / 1000000000000), orderedInterval (5123846910 / 1000000000000) (5123847633 / 1000000000000)))) (orderedInterval (1304759515 / 1000000000000) (1304759717 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate302_chunkChecks3_2 :
    compactCertificate302.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (718032351601539 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55966345495 / 1000000000000) (-55966345494 / 1000000000000), orderedInterval (-20196658184 / 1000000000000) (-20196658183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (608683976443179 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53805709143 / 1000000000000) (53805749732 / 1000000000000), orderedInterval (-36072720618 / 1000000000000) (-36072680028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (380886170354937 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80339121592 / 1000000000000) (80339122016 / 1000000000000), orderedInterval (-15627411195 / 1000000000000) (-15627410770 / 1000000000000)))) (orderedInterval (-4660321171 / 1000000000000) (-4660319623 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (204841849187079 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110119962983 / 1000000000000) (110119963201 / 1000000000000), orderedInterval (-18524144057 / 1000000000000) (-18524143839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (556185467958237 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (67633749140 / 1000000000000) (67633749208 / 1000000000000), orderedInterval (-2272370845 / 1000000000000) (-2272370777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (759423706738749 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48616345911 / 1000000000000) (48616388331 / 1000000000000), orderedInterval (-31586233376 / 1000000000000) (-31586190956 / 1000000000000)))) (orderedInterval (-3129978970 / 1000000000000) (-3129974811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (321113829645063 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51676980057 / 1000000000000) (-51676962308 / 1000000000000), orderedInterval (72845527131 / 1000000000000) (72845544880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1305309889800423 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16663663639 / 1000000000000) (16663663640 / 1000000000000), orderedInterval (40879060184 / 1000000000000) (40879060185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (871886513022057 / 4000000000000) 3 (IntervalRat.scale (351 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49438991563 / 1000000000000) (-49438980640 / 1000000000000), orderedInterval (21940808924 / 1000000000000) (21940819847 / 1000000000000)))) (orderedInterval (29291389992 / 1000000000000) (29291394103 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate302_chunkChecks3 :
    compactCertificate302.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate302.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate302_chunkChecks3_0
    compactCertificate302_chunkChecks3_1 compactCertificate302_chunkChecks3_2

theorem compactCertificate302_chunkChecks4_0 :
    compactCertificate302.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (351 / 2) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20962860211 / 1000000000000) (20962860212 / 1000000000000), orderedInterval (56402943985 / 1000000000000) (56402943986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (517090022713251 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-66631604259 / 1000000000000) (-66631604258 / 1000000000000), orderedInterval (-21761225820 / 1000000000000) (-21761225819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (167216289060483 / 800000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34768174657 / 1000000000000) (34768192086 / 1000000000000), orderedInterval (-42942319775 / 1000000000000) (-42942302346 / 1000000000000)))) (orderedInterval (12435544466 / 1000000000000) (12435546566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (150885578986857 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93582900722 / 1000000000000) (93582900723 / 1000000000000), orderedInterval (88865668021 / 1000000000000) (88865668022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (405299888971029 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (79262425600 / 1000000000000) (79262425637 / 1000000000000), orderedInterval (-975743758 / 1000000000000) (-975743721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1100468040612993 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25478749042 / 1000000000000) (-25478745492 / 1000000000000), orderedInterval (40848650261 / 1000000000000) (40848653812 / 1000000000000)))) (orderedInterval (11129394891 / 1000000000000) (11129396503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (810599777942409 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38969060589 / 1000000000000) (38969100838 / 1000000000000), orderedInterval (-40381229180 / 1000000000000) (-40381188931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1388976535734957 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27176070968 / 1000000000000) (27176080303 / 1000000000000), orderedInterval (-33127056664 / 1000000000000) (-33127047329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1023113829645063 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43206271329 / 1000000000000) (-43206235070 / 1000000000000), orderedInterval (25027720395 / 1000000000000) (25027756654 / 1000000000000)))) (orderedInterval (-17445790646 / 1000000000000) (-17445782121 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate302_chunkChecks4_1 :
    compactCertificate302.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1569719720204649 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19870424333 / 1000000000000) (-19870424332 / 1000000000000), orderedInterval (-35009204766 / 1000000000000) (-35009204765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (906278103012321 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48591276382 / 1000000000000) (48591276383 / 1000000000000), orderedInterval (21075403044 / 1000000000000) (21075403045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1608206397456789 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26023167655 / 1000000000000) (26023167656 / 1000000000000), orderedInterval (30071174302 / 1000000000000) (30071174303 / 1000000000000)))) (orderedInterval (201574170564 / 1000000000000) (201574172076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1502595027551241 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21772938959 / 1000000000000) (-21772936953 / 1000000000000), orderedInterval (34966933816 / 1000000000000) (34966935822 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1072322712619353 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-47100356429 / 1000000000000) (-47100353645 / 1000000000000), orderedInterval (12589245193 / 1000000000000) (12589247977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1215899666913087 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1163017048 / 1000000000000) (-1163017046 / 1000000000000), orderedInterval (-45747043401 / 1000000000000) (-45747043399 / 1000000000000)))) (orderedInterval (-15953290572 / 1000000000000) (-15953288198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1013690378359503 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12957955153 / 1000000000000) (12957955258 / 1000000000000), orderedInterval (-48442332491 / 1000000000000) (-48442332385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (895626191425563 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53200487511 / 1000000000000) (-53200487303 / 1000000000000), orderedInterval (3716001779 / 1000000000000) (3716001986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (259587378982737 / 800000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-44004294036 / 1000000000000) (-44004293313 / 1000000000000), orderedInterval (5123846910 / 1000000000000) (5123847633 / 1000000000000)))) (orderedInterval (-4464484522 / 1000000000000) (-4464484178 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate302_chunkChecks4_2 :
    compactCertificate302.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (718032351601539 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55966345495 / 1000000000000) (-55966345494 / 1000000000000), orderedInterval (-20196658184 / 1000000000000) (-20196658183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (608683976443179 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53805709143 / 1000000000000) (53805749732 / 1000000000000), orderedInterval (-36072720618 / 1000000000000) (-36072680028 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (380886170354937 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (80339121592 / 1000000000000) (80339122016 / 1000000000000), orderedInterval (-15627411195 / 1000000000000) (-15627410770 / 1000000000000)))) (orderedInterval (8352691847 / 1000000000000) (8352693202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (204841849187079 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110119962983 / 1000000000000) (110119963201 / 1000000000000), orderedInterval (-18524144057 / 1000000000000) (-18524143839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (556185467958237 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (67633749140 / 1000000000000) (67633749208 / 1000000000000), orderedInterval (-2272370845 / 1000000000000) (-2272370777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (759423706738749 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48616345911 / 1000000000000) (48616388331 / 1000000000000), orderedInterval (-31586233376 / 1000000000000) (-31586190956 / 1000000000000)))) (orderedInterval (-5686428564 / 1000000000000) (-5686424043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (321113829645063 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51676980057 / 1000000000000) (-51676962308 / 1000000000000), orderedInterval (72845527131 / 1000000000000) (72845544880 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1305309889800423 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16663663639 / 1000000000000) (16663663640 / 1000000000000), orderedInterval (40879060184 / 1000000000000) (40879060185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (871886513022057 / 4000000000000) 4 (IntervalRat.scale (351 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49438991563 / 1000000000000) (-49438980640 / 1000000000000), orderedInterval (21940808924 / 1000000000000) (21940819847 / 1000000000000)))) (orderedInterval (5510176456 / 1000000000000) (5510181634 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate302_chunkChecks4 :
    compactCertificate302.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate302.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate302_chunkChecks4_0
    compactCertificate302_chunkChecks4_1 compactCertificate302_chunkChecks4_2

theorem compactCertificate302_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate302.chunkCheck r b = true :=
  compactCertificate302.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate302_chunkChecks0
    · exact compactCertificate302_chunkChecks1
    · exact compactCertificate302_chunkChecks2
    · exact compactCertificate302_chunkChecks3
    · exact compactCertificate302_chunkChecks4)

theorem compactCertificate302_coefficient0 :
    compactCertificate302.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate302_coefficient1 :
    compactCertificate302.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate302_coefficient2 :
    compactCertificate302.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate302_coefficient3 :
    compactCertificate302.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate302_coefficient4 :
    compactCertificate302.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate302_coefficients : ∀ r : Fin 5,
    compactCertificate302.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate302_coefficient0
  · exact compactCertificate302_coefficient1
  · exact compactCertificate302_coefficient2
  · exact compactCertificate302_coefficient3
  · exact compactCertificate302_coefficient4

theorem compactCertificate302_lower : (1 : ℚ) ≤ compactCertificate302.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate302, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate302_proves {t : ℝ} (ht : t ∈ compactCertificate302.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate302.proves compactCertificate302_states compactCertificate302_chunks
    compactCertificate302_coefficients compactCertificate302_lower ht

end Erdos232
