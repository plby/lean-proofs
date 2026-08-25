/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate568 : CompactCertificate where
  left := 439
  right := 440
  center := 879 / 2
  grid := fun i =>
    match i.val with
    | 0 => 140
    | 1 => 103
    | 2 => 167
    | 3 => 30
    | 4 => 81
    | 5 => 219
    | 6 => 162
    | 7 => 277
    | 8 => 204
    | 9 => 313
    | 10 => 181
    | 11 => 321
    | 12 => 300
    | 13 => 214
    | 14 => 242
    | 15 => 202
    | 16 => 179
    | 17 => 259
    | 18 => 143
    | 19 => 121
    | 20 => 76
    | 21 => 41
    | 22 => 111
    | 23 => 151
    | 24 => 64
    | 25 => 260
    | _ => 174
  point := fun i =>
    match i.val with
    | 0 => 879 / 2
    | 1 => 1294934843204979 / 4000000000000
    | 2 => 418755322177107 / 800000000000
    | 3 => 377858757633753 / 4000000000000
    | 4 => 1014981773235141 / 4000000000000
    | 5 => 2755872956406897 / 4000000000000
    | 6 => 2029963546471161 / 4000000000000
    | 7 => 3478377136498653 / 4000000000000
    | 8 => 2562156855435927 / 4000000000000
    | 9 => 3931007504444121 / 4000000000000
    | 10 => 2269568240877009 / 4000000000000
    | 11 => 4027388670554181 / 4000000000000
    | 12 => 3762908915149689 / 4000000000000
    | 13 => 2685389357243337 / 4000000000000
    | 14 => 3044945319705423 / 4000000000000
    | 15 => 2538557956062687 / 4000000000000
    | 16 => 2242892940920427 / 4000000000000
    | 17 => 650077795230273 / 800000000000
    | 18 => 1798149393326931 / 4000000000000
    | 19 => 1524311154682491 / 4000000000000
    | 20 => 953843144564073 / 4000000000000
    | 21 => 512980015485591 / 4000000000000
    | 22 => 1392840530869773 / 4000000000000
    | 23 => 1901804667303021 / 4000000000000
    | 24 => 804156855435927 / 4000000000000
    | 25 => 3268852971893367 / 4000000000000
    | _ => 2183442293294553 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (16969360396 / 1000000000000) (16969360397 / 1000000000000), orderedInterval (34047548475 / 1000000000000) (34047548476 / 1000000000000))
    | 1 => (orderedInterval (-35671602279 / 1000000000000) (-35671602278 / 1000000000000), orderedInterval (-26289320341 / 1000000000000) (-26289320340 / 1000000000000))
    | 2 => (orderedInterval (14113935287 / 1000000000000) (14113935424 / 1000000000000), orderedInterval (-31904084903 / 1000000000000) (-31904084767 / 1000000000000))
    | 3 => (orderedInterval (69121910817 / 1000000000000) (69121910818 / 1000000000000), orderedInterval (43921363205 / 1000000000000) (43921363206 / 1000000000000))
    | 4 => (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))
    | 5 => (orderedInterval (-29939374878 / 1000000000000) (-29939364317 / 1000000000000), orderedInterval (5280329851 / 1000000000000) (5280340412 / 1000000000000))
    | 6 => (orderedInterval (-21770582005 / 1000000000000) (-21770578952 / 1000000000000), orderedInterval (27958657538 / 1000000000000) (27958660591 / 1000000000000))
    | 7 => (orderedInterval (-4267240991 / 1000000000000) (-4267240990 / 1000000000000), orderedInterval (-26716061278 / 1000000000000) (-26716061277 / 1000000000000))
    | 8 => (orderedInterval (13414294058 / 1000000000000) (13414294059 / 1000000000000), orderedInterval (28519126456 / 1000000000000) (28519126457 / 1000000000000))
    | 9 => (orderedInterval (-5520707913 / 1000000000000) (-5520707912 / 1000000000000), orderedInterval (-24843012703 / 1000000000000) (-24843012702 / 1000000000000))
    | 10 => (orderedInterval (14600912565 / 1000000000000) (14600912726 / 1000000000000), orderedInterval (-30159574447 / 1000000000000) (-30159574286 / 1000000000000))
    | 11 => (orderedInterval (18364345232 / 1000000000000) (18364346252 / 1000000000000), orderedInterval (-17185882850 / 1000000000000) (-17185881830 / 1000000000000))
    | 12 => (orderedInterval (-21389307738 / 1000000000000) (-21389300349 / 1000000000000), orderedInterval (14817753941 / 1000000000000) (14817761330 / 1000000000000))
    | 13 => (orderedInterval (-5157490865 / 1000000000000) (-5157490863 / 1000000000000), orderedInterval (30362898604 / 1000000000000) (30362898606 / 1000000000000))
    | 14 => (orderedInterval (28423488775 / 1000000000000) (28423505661 / 1000000000000), orderedInterval (-5348009148 / 1000000000000) (-5347992262 / 1000000000000))
    | 15 => (orderedInterval (23221063797 / 1000000000000) (23221063798 / 1000000000000), orderedInterval (21520101287 / 1000000000000) (21520101288 / 1000000000000))
    | 16 => (orderedInterval (25015827375 / 1000000000000) (25015841355 / 1000000000000), orderedInterval (-22595809049 / 1000000000000) (-22595795070 / 1000000000000))
    | 17 => (orderedInterval (8004031505 / 1000000000000) (8004031507 / 1000000000000), orderedInterval (-26826070832 / 1000000000000) (-26826070829 / 1000000000000))
    | 18 => (orderedInterval (-33095683988 / 1000000000000) (-33095683987 / 1000000000000), orderedInterval (-17875246874 / 1000000000000) (-17875246873 / 1000000000000))
    | 19 => (orderedInterval (-40354835212 / 1000000000000) (-40354833491 / 1000000000000), orderedInterval (6538541598 / 1000000000000) (6538543319 / 1000000000000))
    | 20 => (orderedInterval (24071134577 / 1000000000000) (24071134578 / 1000000000000), orderedInterval (45669196345 / 1000000000000) (45669196346 / 1000000000000))
    | 21 => (orderedInterval (-15659333335 / 1000000000000) (-15659333334 / 1000000000000), orderedInterval (-68633267932 / 1000000000000) (-68633267931 / 1000000000000))
    | 22 => (orderedInterval (-11750178796 / 1000000000000) (-11750178795 / 1000000000000), orderedInterval (-41095146717 / 1000000000000) (-41095146716 / 1000000000000))
    | 23 => (orderedInterval (-35115857047 / 1000000000000) (-35115846175 / 1000000000000), orderedInterval (10325591259 / 1000000000000) (10325602131 / 1000000000000))
    | 24 => (orderedInterval (38851540951 / 1000000000000) (38851540952 / 1000000000000), orderedInterval (40612131837 / 1000000000000) (40612131838 / 1000000000000))
    | 25 => (orderedInterval (25853007767 / 1000000000000) (25853007790 / 1000000000000), orderedInterval (10502495950 / 1000000000000) (10502495973 / 1000000000000))
    | _ => (orderedInterval (294401226 / 1000000000000) (294401227 / 1000000000000), orderedInterval (34149136106 / 1000000000000) (34149136107 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (7221892081 / 1000000000000) (7221892121 / 1000000000000)
      | 1 => orderedInterval (1266337722 / 1000000000000) (1266338526 / 1000000000000)
      | 2 => orderedInterval (455815794 / 1000000000000) (455815819 / 1000000000000)
      | 3 => orderedInterval (4673370399 / 1000000000000) (4673370731 / 1000000000000)
      | 4 => orderedInterval (-245403576 / 1000000000000) (-245403304 / 1000000000000)
      | 5 => orderedInterval (-958489490 / 1000000000000) (-958488648 / 1000000000000)
      | 6 => orderedInterval (8359473787 / 1000000000000) (8359473995 / 1000000000000)
      | 7 => orderedInterval (3246964851 / 1000000000000) (3246965737 / 1000000000000)
      | _ => orderedInterval (-1925508483 / 1000000000000) (-1925508359 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11085065148 / 1000000000000) (11085065193 / 1000000000000)
      | 1 => orderedInterval (-1744632787 / 1000000000000) (-1744631550 / 1000000000000)
      | 2 => orderedInterval (2634958511 / 1000000000000) (2634958555 / 1000000000000)
      | 3 => orderedInterval (1389036139 / 1000000000000) (1389036848 / 1000000000000)
      | 4 => orderedInterval (3860127063 / 1000000000000) (3860127582 / 1000000000000)
      | 5 => orderedInterval (738654086 / 1000000000000) (738655168 / 1000000000000)
      | 6 => orderedInterval (3409186762 / 1000000000000) (3409186949 / 1000000000000)
      | 7 => orderedInterval (252391709 / 1000000000000) (252392658 / 1000000000000)
      | _ => orderedInterval (-9435535886 / 1000000000000) (-9435535711 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-7745751909 / 1000000000000) (-7745751858 / 1000000000000)
      | 1 => orderedInterval (-5154350503 / 1000000000000) (-5154348572 / 1000000000000)
      | 2 => orderedInterval (-1209888624 / 1000000000000) (-1209888547 / 1000000000000)
      | 3 => orderedInterval (-20411907578 / 1000000000000) (-20411906022 / 1000000000000)
      | 4 => orderedInterval (-208404392 / 1000000000000) (-208403382 / 1000000000000)
      | 5 => orderedInterval (1068821313 / 1000000000000) (1068822709 / 1000000000000)
      | 6 => orderedInterval (-7491867935 / 1000000000000) (-7491867764 / 1000000000000)
      | 7 => orderedInterval (-3342063247 / 1000000000000) (-3342062222 / 1000000000000)
      | _ => orderedInterval (7333759419 / 1000000000000) (7333759678 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10216818056 / 1000000000000) (-10216817996 / 1000000000000)
      | 1 => orderedInterval (1813771492 / 1000000000000) (1813774513 / 1000000000000)
      | 2 => orderedInterval (-8513833905 / 1000000000000) (-8513833765 / 1000000000000)
      | 3 => orderedInterval (-15125757627 / 1000000000000) (-15125754159 / 1000000000000)
      | 4 => orderedInterval (-7750446424 / 1000000000000) (-7750444430 / 1000000000000)
      | 5 => orderedInterval (905247837 / 1000000000000) (905249642 / 1000000000000)
      | 6 => orderedInterval (-3037610071 / 1000000000000) (-3037609913 / 1000000000000)
      | 7 => orderedInterval (514300338 / 1000000000000) (514301444 / 1000000000000)
      | _ => orderedInterval (17731542381 / 1000000000000) (17731542783 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (8341113325 / 1000000000000) (8341113395 / 1000000000000)
      | 1 => orderedInterval (12830829489 / 1000000000000) (12830834228 / 1000000000000)
      | 2 => orderedInterval (3518641154 / 1000000000000) (3518641411 / 1000000000000)
      | 3 => orderedInterval (99502809359 / 1000000000000) (99502817163 / 1000000000000)
      | 4 => orderedInterval (4190687777 / 1000000000000) (4190691769 / 1000000000000)
      | 5 => orderedInterval (-236286200 / 1000000000000) (-236283851 / 1000000000000)
      | 6 => orderedInterval (7164687842 / 1000000000000) (7164687990 / 1000000000000)
      | 7 => orderedInterval (3790650323 / 1000000000000) (3790651520 / 1000000000000)
      | _ => orderedInterval (-25358384093 / 1000000000000) (-25358383445 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (22094453085 / 1000000000000) (22094456618 / 1000000000000)
    | 1 => orderedInterval (12189250745 / 1000000000000) (12189255692 / 1000000000000)
    | 2 => orderedInterval (-37161653456 / 1000000000000) (-37161645980 / 1000000000000)
    | 3 => orderedInterval (-23679604035 / 1000000000000) (-23679591881 / 1000000000000)
    | _ => orderedInterval (113744748976 / 1000000000000) (113744770180 / 1000000000000)

theorem compactCertificate568_stateChecks0 :
    compactCertificate568.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (879 / 2)) (orderedInterval (16969360396 / 1000000000000) (16969360397 / 1000000000000), orderedInterval (34047548475 / 1000000000000) (34047548476 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1294934843204979 / 4000000000000)) (orderedInterval (-35671602279 / 1000000000000) (-35671602278 / 1000000000000), orderedInterval (-26289320341 / 1000000000000) (-26289320340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (418755322177107 / 800000000000)) (orderedInterval (14113935287 / 1000000000000) (14113935424 / 1000000000000), orderedInterval (-31904084903 / 1000000000000) (-31904084767 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_stateChecks1 :
    compactCertificate568.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (377858757633753 / 4000000000000)) (orderedInterval (69121910817 / 1000000000000) (69121910818 / 1000000000000), orderedInterval (43921363205 / 1000000000000) (43921363206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1014981773235141 / 4000000000000)) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2755872956406897 / 4000000000000)) (orderedInterval (-29939374878 / 1000000000000) (-29939364317 / 1000000000000), orderedInterval (5280329851 / 1000000000000) (5280340412 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_stateChecks2 :
    compactCertificate568.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2029963546471161 / 4000000000000)) (orderedInterval (-21770582005 / 1000000000000) (-21770578952 / 1000000000000), orderedInterval (27958657538 / 1000000000000) (27958660591 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 277 12 (3478377136498653 / 4000000000000)) (orderedInterval (-4267240991 / 1000000000000) (-4267240990 / 1000000000000), orderedInterval (-26716061278 / 1000000000000) (-26716061277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2562156855435927 / 4000000000000)) (orderedInterval (13414294058 / 1000000000000) (13414294059 / 1000000000000), orderedInterval (28519126456 / 1000000000000) (28519126457 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_stateChecks3 :
    compactCertificate568.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 313 12 (3931007504444121 / 4000000000000)) (orderedInterval (-5520707913 / 1000000000000) (-5520707912 / 1000000000000), orderedInterval (-24843012703 / 1000000000000) (-24843012702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2269568240877009 / 4000000000000)) (orderedInterval (14600912565 / 1000000000000) (14600912726 / 1000000000000), orderedInterval (-30159574447 / 1000000000000) (-30159574286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 321 12 (4027388670554181 / 4000000000000)) (orderedInterval (18364345232 / 1000000000000) (18364346252 / 1000000000000), orderedInterval (-17185882850 / 1000000000000) (-17185881830 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_stateChecks4 :
    compactCertificate568.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 300 12 (3762908915149689 / 4000000000000)) (orderedInterval (-21389307738 / 1000000000000) (-21389300349 / 1000000000000), orderedInterval (14817753941 / 1000000000000) (14817761330 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2685389357243337 / 4000000000000)) (orderedInterval (-5157490865 / 1000000000000) (-5157490863 / 1000000000000), orderedInterval (30362898604 / 1000000000000) (30362898606 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3044945319705423 / 4000000000000)) (orderedInterval (28423488775 / 1000000000000) (28423505661 / 1000000000000), orderedInterval (-5348009148 / 1000000000000) (-5347992262 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_stateChecks5 :
    compactCertificate568.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2538557956062687 / 4000000000000)) (orderedInterval (23221063797 / 1000000000000) (23221063798 / 1000000000000), orderedInterval (21520101287 / 1000000000000) (21520101288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2242892940920427 / 4000000000000)) (orderedInterval (25015827375 / 1000000000000) (25015841355 / 1000000000000), orderedInterval (-22595809049 / 1000000000000) (-22595795070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (650077795230273 / 800000000000)) (orderedInterval (8004031505 / 1000000000000) (8004031507 / 1000000000000), orderedInterval (-26826070832 / 1000000000000) (-26826070829 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_stateChecks6 :
    compactCertificate568.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1798149393326931 / 4000000000000)) (orderedInterval (-33095683988 / 1000000000000) (-33095683987 / 1000000000000), orderedInterval (-17875246874 / 1000000000000) (-17875246873 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1524311154682491 / 4000000000000)) (orderedInterval (-40354835212 / 1000000000000) (-40354833491 / 1000000000000), orderedInterval (6538541598 / 1000000000000) (6538543319 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (953843144564073 / 4000000000000)) (orderedInterval (24071134577 / 1000000000000) (24071134578 / 1000000000000), orderedInterval (45669196345 / 1000000000000) (45669196346 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_stateChecks7 :
    compactCertificate568.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (512980015485591 / 4000000000000)) (orderedInterval (-15659333335 / 1000000000000) (-15659333334 / 1000000000000), orderedInterval (-68633267932 / 1000000000000) (-68633267931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1392840530869773 / 4000000000000)) (orderedInterval (-11750178796 / 1000000000000) (-11750178795 / 1000000000000), orderedInterval (-41095146717 / 1000000000000) (-41095146716 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1901804667303021 / 4000000000000)) (orderedInterval (-35115857047 / 1000000000000) (-35115846175 / 1000000000000), orderedInterval (10325591259 / 1000000000000) (10325602131 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_stateChecks8 :
    compactCertificate568.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (804156855435927 / 4000000000000)) (orderedInterval (38851540951 / 1000000000000) (38851540952 / 1000000000000), orderedInterval (40612131837 / 1000000000000) (40612131838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (3268852971893367 / 4000000000000)) (orderedInterval (25853007767 / 1000000000000) (25853007790 / 1000000000000), orderedInterval (10502495950 / 1000000000000) (10502495973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2183442293294553 / 4000000000000)) (orderedInterval (294401226 / 1000000000000) (294401227 / 1000000000000), orderedInterval (34149136106 / 1000000000000) (34149136107 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_states : ∀ j,
    BesselStateValid (compactCertificate568.point j) (compactCertificate568.state j) :=
  compactCertificate568.statesValid_of_checks3 compactCertificate568_stateChecks0
    compactCertificate568_stateChecks1 compactCertificate568_stateChecks2
    compactCertificate568_stateChecks3 compactCertificate568_stateChecks4
    compactCertificate568_stateChecks5 compactCertificate568_stateChecks6
    compactCertificate568_stateChecks7 compactCertificate568_stateChecks8

theorem compactCertificate568_chunkChecks0_0 :
    compactCertificate568.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (879 / 2) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16969360396 / 1000000000000) (16969360397 / 1000000000000), orderedInterval (34047548475 / 1000000000000) (34047548476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1294934843204979 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35671602279 / 1000000000000) (-35671602278 / 1000000000000), orderedInterval (-26289320341 / 1000000000000) (-26289320340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (418755322177107 / 800000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14113935287 / 1000000000000) (14113935424 / 1000000000000), orderedInterval (-31904084903 / 1000000000000) (-31904084767 / 1000000000000)))) (orderedInterval (7221892081 / 1000000000000) (7221892121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (377858757633753 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69121910817 / 1000000000000) (69121910818 / 1000000000000), orderedInterval (43921363205 / 1000000000000) (43921363206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2755872956406897 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29939374878 / 1000000000000) (-29939364317 / 1000000000000), orderedInterval (5280329851 / 1000000000000) (5280340412 / 1000000000000)))) (orderedInterval (1266337722 / 1000000000000) (1266338526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2029963546471161 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21770582005 / 1000000000000) (-21770578952 / 1000000000000), orderedInterval (27958657538 / 1000000000000) (27958660591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3478377136498653 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4267240991 / 1000000000000) (-4267240990 / 1000000000000), orderedInterval (-26716061278 / 1000000000000) (-26716061277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2562156855435927 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13414294058 / 1000000000000) (13414294059 / 1000000000000), orderedInterval (28519126456 / 1000000000000) (28519126457 / 1000000000000)))) (orderedInterval (455815794 / 1000000000000) (455815819 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks0_1 :
    compactCertificate568.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3931007504444121 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5520707913 / 1000000000000) (-5520707912 / 1000000000000), orderedInterval (-24843012703 / 1000000000000) (-24843012702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2269568240877009 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14600912565 / 1000000000000) (14600912726 / 1000000000000), orderedInterval (-30159574447 / 1000000000000) (-30159574286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4027388670554181 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18364345232 / 1000000000000) (18364346252 / 1000000000000), orderedInterval (-17185882850 / 1000000000000) (-17185881830 / 1000000000000)))) (orderedInterval (4673370399 / 1000000000000) (4673370731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3762908915149689 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21389307738 / 1000000000000) (-21389300349 / 1000000000000), orderedInterval (14817753941 / 1000000000000) (14817761330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2685389357243337 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5157490865 / 1000000000000) (-5157490863 / 1000000000000), orderedInterval (30362898604 / 1000000000000) (30362898606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3044945319705423 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28423488775 / 1000000000000) (28423505661 / 1000000000000), orderedInterval (-5348009148 / 1000000000000) (-5347992262 / 1000000000000)))) (orderedInterval (-245403576 / 1000000000000) (-245403304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2538557956062687 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23221063797 / 1000000000000) (23221063798 / 1000000000000), orderedInterval (21520101287 / 1000000000000) (21520101288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2242892940920427 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25015827375 / 1000000000000) (25015841355 / 1000000000000), orderedInterval (-22595809049 / 1000000000000) (-22595795070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (650077795230273 / 800000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8004031505 / 1000000000000) (8004031507 / 1000000000000), orderedInterval (-26826070832 / 1000000000000) (-26826070829 / 1000000000000)))) (orderedInterval (-958489490 / 1000000000000) (-958488648 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks0_2 :
    compactCertificate568.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1798149393326931 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33095683988 / 1000000000000) (-33095683987 / 1000000000000), orderedInterval (-17875246874 / 1000000000000) (-17875246873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1524311154682491 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40354835212 / 1000000000000) (-40354833491 / 1000000000000), orderedInterval (6538541598 / 1000000000000) (6538543319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (953843144564073 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24071134577 / 1000000000000) (24071134578 / 1000000000000), orderedInterval (45669196345 / 1000000000000) (45669196346 / 1000000000000)))) (orderedInterval (8359473787 / 1000000000000) (8359473995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (512980015485591 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15659333335 / 1000000000000) (-15659333334 / 1000000000000), orderedInterval (-68633267932 / 1000000000000) (-68633267931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1392840530869773 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11750178796 / 1000000000000) (-11750178795 / 1000000000000), orderedInterval (-41095146717 / 1000000000000) (-41095146716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1901804667303021 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35115857047 / 1000000000000) (-35115846175 / 1000000000000), orderedInterval (10325591259 / 1000000000000) (10325602131 / 1000000000000)))) (orderedInterval (3246964851 / 1000000000000) (3246965737 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (804156855435927 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38851540951 / 1000000000000) (38851540952 / 1000000000000), orderedInterval (40612131837 / 1000000000000) (40612131838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3268852971893367 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25853007767 / 1000000000000) (25853007790 / 1000000000000), orderedInterval (10502495950 / 1000000000000) (10502495973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2183442293294553 / 4000000000000) 0 (IntervalRat.scale (879 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (294401226 / 1000000000000) (294401227 / 1000000000000), orderedInterval (34149136106 / 1000000000000) (34149136107 / 1000000000000)))) (orderedInterval (-1925508483 / 1000000000000) (-1925508359 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks0 :
    compactCertificate568.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate568.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate568_chunkChecks0_0
    compactCertificate568_chunkChecks0_1 compactCertificate568_chunkChecks0_2

theorem compactCertificate568_chunkChecks1_0 :
    compactCertificate568.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (879 / 2) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16969360396 / 1000000000000) (16969360397 / 1000000000000), orderedInterval (34047548475 / 1000000000000) (34047548476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1294934843204979 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35671602279 / 1000000000000) (-35671602278 / 1000000000000), orderedInterval (-26289320341 / 1000000000000) (-26289320340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (418755322177107 / 800000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14113935287 / 1000000000000) (14113935424 / 1000000000000), orderedInterval (-31904084903 / 1000000000000) (-31904084767 / 1000000000000)))) (orderedInterval (11085065148 / 1000000000000) (11085065193 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (377858757633753 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69121910817 / 1000000000000) (69121910818 / 1000000000000), orderedInterval (43921363205 / 1000000000000) (43921363206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2755872956406897 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29939374878 / 1000000000000) (-29939364317 / 1000000000000), orderedInterval (5280329851 / 1000000000000) (5280340412 / 1000000000000)))) (orderedInterval (-1744632787 / 1000000000000) (-1744631550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2029963546471161 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21770582005 / 1000000000000) (-21770578952 / 1000000000000), orderedInterval (27958657538 / 1000000000000) (27958660591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3478377136498653 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4267240991 / 1000000000000) (-4267240990 / 1000000000000), orderedInterval (-26716061278 / 1000000000000) (-26716061277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2562156855435927 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13414294058 / 1000000000000) (13414294059 / 1000000000000), orderedInterval (28519126456 / 1000000000000) (28519126457 / 1000000000000)))) (orderedInterval (2634958511 / 1000000000000) (2634958555 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks1_1 :
    compactCertificate568.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3931007504444121 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5520707913 / 1000000000000) (-5520707912 / 1000000000000), orderedInterval (-24843012703 / 1000000000000) (-24843012702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2269568240877009 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14600912565 / 1000000000000) (14600912726 / 1000000000000), orderedInterval (-30159574447 / 1000000000000) (-30159574286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4027388670554181 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18364345232 / 1000000000000) (18364346252 / 1000000000000), orderedInterval (-17185882850 / 1000000000000) (-17185881830 / 1000000000000)))) (orderedInterval (1389036139 / 1000000000000) (1389036848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3762908915149689 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21389307738 / 1000000000000) (-21389300349 / 1000000000000), orderedInterval (14817753941 / 1000000000000) (14817761330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2685389357243337 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5157490865 / 1000000000000) (-5157490863 / 1000000000000), orderedInterval (30362898604 / 1000000000000) (30362898606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3044945319705423 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28423488775 / 1000000000000) (28423505661 / 1000000000000), orderedInterval (-5348009148 / 1000000000000) (-5347992262 / 1000000000000)))) (orderedInterval (3860127063 / 1000000000000) (3860127582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2538557956062687 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23221063797 / 1000000000000) (23221063798 / 1000000000000), orderedInterval (21520101287 / 1000000000000) (21520101288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2242892940920427 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25015827375 / 1000000000000) (25015841355 / 1000000000000), orderedInterval (-22595809049 / 1000000000000) (-22595795070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (650077795230273 / 800000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8004031505 / 1000000000000) (8004031507 / 1000000000000), orderedInterval (-26826070832 / 1000000000000) (-26826070829 / 1000000000000)))) (orderedInterval (738654086 / 1000000000000) (738655168 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks1_2 :
    compactCertificate568.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1798149393326931 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33095683988 / 1000000000000) (-33095683987 / 1000000000000), orderedInterval (-17875246874 / 1000000000000) (-17875246873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1524311154682491 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40354835212 / 1000000000000) (-40354833491 / 1000000000000), orderedInterval (6538541598 / 1000000000000) (6538543319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (953843144564073 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24071134577 / 1000000000000) (24071134578 / 1000000000000), orderedInterval (45669196345 / 1000000000000) (45669196346 / 1000000000000)))) (orderedInterval (3409186762 / 1000000000000) (3409186949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (512980015485591 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15659333335 / 1000000000000) (-15659333334 / 1000000000000), orderedInterval (-68633267932 / 1000000000000) (-68633267931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1392840530869773 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11750178796 / 1000000000000) (-11750178795 / 1000000000000), orderedInterval (-41095146717 / 1000000000000) (-41095146716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1901804667303021 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35115857047 / 1000000000000) (-35115846175 / 1000000000000), orderedInterval (10325591259 / 1000000000000) (10325602131 / 1000000000000)))) (orderedInterval (252391709 / 1000000000000) (252392658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (804156855435927 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38851540951 / 1000000000000) (38851540952 / 1000000000000), orderedInterval (40612131837 / 1000000000000) (40612131838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3268852971893367 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25853007767 / 1000000000000) (25853007790 / 1000000000000), orderedInterval (10502495950 / 1000000000000) (10502495973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2183442293294553 / 4000000000000) 1 (IntervalRat.scale (879 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (294401226 / 1000000000000) (294401227 / 1000000000000), orderedInterval (34149136106 / 1000000000000) (34149136107 / 1000000000000)))) (orderedInterval (-9435535886 / 1000000000000) (-9435535711 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks1 :
    compactCertificate568.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate568.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate568_chunkChecks1_0
    compactCertificate568_chunkChecks1_1 compactCertificate568_chunkChecks1_2

theorem compactCertificate568_chunkChecks2_0 :
    compactCertificate568.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (879 / 2) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16969360396 / 1000000000000) (16969360397 / 1000000000000), orderedInterval (34047548475 / 1000000000000) (34047548476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1294934843204979 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35671602279 / 1000000000000) (-35671602278 / 1000000000000), orderedInterval (-26289320341 / 1000000000000) (-26289320340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (418755322177107 / 800000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14113935287 / 1000000000000) (14113935424 / 1000000000000), orderedInterval (-31904084903 / 1000000000000) (-31904084767 / 1000000000000)))) (orderedInterval (-7745751909 / 1000000000000) (-7745751858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (377858757633753 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69121910817 / 1000000000000) (69121910818 / 1000000000000), orderedInterval (43921363205 / 1000000000000) (43921363206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2755872956406897 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29939374878 / 1000000000000) (-29939364317 / 1000000000000), orderedInterval (5280329851 / 1000000000000) (5280340412 / 1000000000000)))) (orderedInterval (-5154350503 / 1000000000000) (-5154348572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2029963546471161 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21770582005 / 1000000000000) (-21770578952 / 1000000000000), orderedInterval (27958657538 / 1000000000000) (27958660591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3478377136498653 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4267240991 / 1000000000000) (-4267240990 / 1000000000000), orderedInterval (-26716061278 / 1000000000000) (-26716061277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2562156855435927 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13414294058 / 1000000000000) (13414294059 / 1000000000000), orderedInterval (28519126456 / 1000000000000) (28519126457 / 1000000000000)))) (orderedInterval (-1209888624 / 1000000000000) (-1209888547 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks2_1 :
    compactCertificate568.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3931007504444121 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5520707913 / 1000000000000) (-5520707912 / 1000000000000), orderedInterval (-24843012703 / 1000000000000) (-24843012702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2269568240877009 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14600912565 / 1000000000000) (14600912726 / 1000000000000), orderedInterval (-30159574447 / 1000000000000) (-30159574286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4027388670554181 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18364345232 / 1000000000000) (18364346252 / 1000000000000), orderedInterval (-17185882850 / 1000000000000) (-17185881830 / 1000000000000)))) (orderedInterval (-20411907578 / 1000000000000) (-20411906022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3762908915149689 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21389307738 / 1000000000000) (-21389300349 / 1000000000000), orderedInterval (14817753941 / 1000000000000) (14817761330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2685389357243337 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5157490865 / 1000000000000) (-5157490863 / 1000000000000), orderedInterval (30362898604 / 1000000000000) (30362898606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3044945319705423 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28423488775 / 1000000000000) (28423505661 / 1000000000000), orderedInterval (-5348009148 / 1000000000000) (-5347992262 / 1000000000000)))) (orderedInterval (-208404392 / 1000000000000) (-208403382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2538557956062687 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23221063797 / 1000000000000) (23221063798 / 1000000000000), orderedInterval (21520101287 / 1000000000000) (21520101288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2242892940920427 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25015827375 / 1000000000000) (25015841355 / 1000000000000), orderedInterval (-22595809049 / 1000000000000) (-22595795070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (650077795230273 / 800000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8004031505 / 1000000000000) (8004031507 / 1000000000000), orderedInterval (-26826070832 / 1000000000000) (-26826070829 / 1000000000000)))) (orderedInterval (1068821313 / 1000000000000) (1068822709 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks2_2 :
    compactCertificate568.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1798149393326931 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33095683988 / 1000000000000) (-33095683987 / 1000000000000), orderedInterval (-17875246874 / 1000000000000) (-17875246873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1524311154682491 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40354835212 / 1000000000000) (-40354833491 / 1000000000000), orderedInterval (6538541598 / 1000000000000) (6538543319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (953843144564073 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24071134577 / 1000000000000) (24071134578 / 1000000000000), orderedInterval (45669196345 / 1000000000000) (45669196346 / 1000000000000)))) (orderedInterval (-7491867935 / 1000000000000) (-7491867764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (512980015485591 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15659333335 / 1000000000000) (-15659333334 / 1000000000000), orderedInterval (-68633267932 / 1000000000000) (-68633267931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1392840530869773 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11750178796 / 1000000000000) (-11750178795 / 1000000000000), orderedInterval (-41095146717 / 1000000000000) (-41095146716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1901804667303021 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35115857047 / 1000000000000) (-35115846175 / 1000000000000), orderedInterval (10325591259 / 1000000000000) (10325602131 / 1000000000000)))) (orderedInterval (-3342063247 / 1000000000000) (-3342062222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (804156855435927 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38851540951 / 1000000000000) (38851540952 / 1000000000000), orderedInterval (40612131837 / 1000000000000) (40612131838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3268852971893367 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25853007767 / 1000000000000) (25853007790 / 1000000000000), orderedInterval (10502495950 / 1000000000000) (10502495973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2183442293294553 / 4000000000000) 2 (IntervalRat.scale (879 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (294401226 / 1000000000000) (294401227 / 1000000000000), orderedInterval (34149136106 / 1000000000000) (34149136107 / 1000000000000)))) (orderedInterval (7333759419 / 1000000000000) (7333759678 / 1000000000000))) = true
  rfl'

theorem compactCertificate568_chunkChecks2 :
    compactCertificate568.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate568.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate568_chunkChecks2_0
    compactCertificate568_chunkChecks2_1 compactCertificate568_chunkChecks2_2

theorem compactCertificate568_chunkChecks3_0 :
    compactCertificate568.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (879 / 2) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16969360396 / 1000000000000) (16969360397 / 1000000000000), orderedInterval (34047548475 / 1000000000000) (34047548476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1294934843204979 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35671602279 / 1000000000000) (-35671602278 / 1000000000000), orderedInterval (-26289320341 / 1000000000000) (-26289320340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (418755322177107 / 800000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14113935287 / 1000000000000) (14113935424 / 1000000000000), orderedInterval (-31904084903 / 1000000000000) (-31904084767 / 1000000000000)))) (orderedInterval (-10216818056 / 1000000000000) (-10216817996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (377858757633753 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69121910817 / 1000000000000) (69121910818 / 1000000000000), orderedInterval (43921363205 / 1000000000000) (43921363206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2755872956406897 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29939374878 / 1000000000000) (-29939364317 / 1000000000000), orderedInterval (5280329851 / 1000000000000) (5280340412 / 1000000000000)))) (orderedInterval (1813771492 / 1000000000000) (1813774513 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2029963546471161 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21770582005 / 1000000000000) (-21770578952 / 1000000000000), orderedInterval (27958657538 / 1000000000000) (27958660591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3478377136498653 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4267240991 / 1000000000000) (-4267240990 / 1000000000000), orderedInterval (-26716061278 / 1000000000000) (-26716061277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2562156855435927 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13414294058 / 1000000000000) (13414294059 / 1000000000000), orderedInterval (28519126456 / 1000000000000) (28519126457 / 1000000000000)))) (orderedInterval (-8513833905 / 1000000000000) (-8513833765 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate568_chunkChecks3_1 :
    compactCertificate568.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3931007504444121 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5520707913 / 1000000000000) (-5520707912 / 1000000000000), orderedInterval (-24843012703 / 1000000000000) (-24843012702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2269568240877009 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14600912565 / 1000000000000) (14600912726 / 1000000000000), orderedInterval (-30159574447 / 1000000000000) (-30159574286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4027388670554181 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18364345232 / 1000000000000) (18364346252 / 1000000000000), orderedInterval (-17185882850 / 1000000000000) (-17185881830 / 1000000000000)))) (orderedInterval (-15125757627 / 1000000000000) (-15125754159 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3762908915149689 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21389307738 / 1000000000000) (-21389300349 / 1000000000000), orderedInterval (14817753941 / 1000000000000) (14817761330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2685389357243337 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5157490865 / 1000000000000) (-5157490863 / 1000000000000), orderedInterval (30362898604 / 1000000000000) (30362898606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3044945319705423 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28423488775 / 1000000000000) (28423505661 / 1000000000000), orderedInterval (-5348009148 / 1000000000000) (-5347992262 / 1000000000000)))) (orderedInterval (-7750446424 / 1000000000000) (-7750444430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2538557956062687 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23221063797 / 1000000000000) (23221063798 / 1000000000000), orderedInterval (21520101287 / 1000000000000) (21520101288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2242892940920427 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25015827375 / 1000000000000) (25015841355 / 1000000000000), orderedInterval (-22595809049 / 1000000000000) (-22595795070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (650077795230273 / 800000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8004031505 / 1000000000000) (8004031507 / 1000000000000), orderedInterval (-26826070832 / 1000000000000) (-26826070829 / 1000000000000)))) (orderedInterval (905247837 / 1000000000000) (905249642 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate568_chunkChecks3_2 :
    compactCertificate568.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1798149393326931 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33095683988 / 1000000000000) (-33095683987 / 1000000000000), orderedInterval (-17875246874 / 1000000000000) (-17875246873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1524311154682491 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40354835212 / 1000000000000) (-40354833491 / 1000000000000), orderedInterval (6538541598 / 1000000000000) (6538543319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (953843144564073 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24071134577 / 1000000000000) (24071134578 / 1000000000000), orderedInterval (45669196345 / 1000000000000) (45669196346 / 1000000000000)))) (orderedInterval (-3037610071 / 1000000000000) (-3037609913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (512980015485591 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15659333335 / 1000000000000) (-15659333334 / 1000000000000), orderedInterval (-68633267932 / 1000000000000) (-68633267931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1392840530869773 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11750178796 / 1000000000000) (-11750178795 / 1000000000000), orderedInterval (-41095146717 / 1000000000000) (-41095146716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1901804667303021 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35115857047 / 1000000000000) (-35115846175 / 1000000000000), orderedInterval (10325591259 / 1000000000000) (10325602131 / 1000000000000)))) (orderedInterval (514300338 / 1000000000000) (514301444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (804156855435927 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38851540951 / 1000000000000) (38851540952 / 1000000000000), orderedInterval (40612131837 / 1000000000000) (40612131838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3268852971893367 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25853007767 / 1000000000000) (25853007790 / 1000000000000), orderedInterval (10502495950 / 1000000000000) (10502495973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2183442293294553 / 4000000000000) 3 (IntervalRat.scale (879 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (294401226 / 1000000000000) (294401227 / 1000000000000), orderedInterval (34149136106 / 1000000000000) (34149136107 / 1000000000000)))) (orderedInterval (17731542381 / 1000000000000) (17731542783 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate568_chunkChecks3 :
    compactCertificate568.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate568.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate568_chunkChecks3_0
    compactCertificate568_chunkChecks3_1 compactCertificate568_chunkChecks3_2

theorem compactCertificate568_chunkChecks4_0 :
    compactCertificate568.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (879 / 2) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16969360396 / 1000000000000) (16969360397 / 1000000000000), orderedInterval (34047548475 / 1000000000000) (34047548476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1294934843204979 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35671602279 / 1000000000000) (-35671602278 / 1000000000000), orderedInterval (-26289320341 / 1000000000000) (-26289320340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (418755322177107 / 800000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14113935287 / 1000000000000) (14113935424 / 1000000000000), orderedInterval (-31904084903 / 1000000000000) (-31904084767 / 1000000000000)))) (orderedInterval (8341113325 / 1000000000000) (8341113395 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (377858757633753 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (69121910817 / 1000000000000) (69121910818 / 1000000000000), orderedInterval (43921363205 / 1000000000000) (43921363206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2755872956406897 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29939374878 / 1000000000000) (-29939364317 / 1000000000000), orderedInterval (5280329851 / 1000000000000) (5280340412 / 1000000000000)))) (orderedInterval (12830829489 / 1000000000000) (12830834228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2029963546471161 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21770582005 / 1000000000000) (-21770578952 / 1000000000000), orderedInterval (27958657538 / 1000000000000) (27958660591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3478377136498653 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4267240991 / 1000000000000) (-4267240990 / 1000000000000), orderedInterval (-26716061278 / 1000000000000) (-26716061277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2562156855435927 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13414294058 / 1000000000000) (13414294059 / 1000000000000), orderedInterval (28519126456 / 1000000000000) (28519126457 / 1000000000000)))) (orderedInterval (3518641154 / 1000000000000) (3518641411 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate568_chunkChecks4_1 :
    compactCertificate568.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3931007504444121 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5520707913 / 1000000000000) (-5520707912 / 1000000000000), orderedInterval (-24843012703 / 1000000000000) (-24843012702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2269568240877009 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14600912565 / 1000000000000) (14600912726 / 1000000000000), orderedInterval (-30159574447 / 1000000000000) (-30159574286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4027388670554181 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18364345232 / 1000000000000) (18364346252 / 1000000000000), orderedInterval (-17185882850 / 1000000000000) (-17185881830 / 1000000000000)))) (orderedInterval (99502809359 / 1000000000000) (99502817163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3762908915149689 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21389307738 / 1000000000000) (-21389300349 / 1000000000000), orderedInterval (14817753941 / 1000000000000) (14817761330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2685389357243337 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5157490865 / 1000000000000) (-5157490863 / 1000000000000), orderedInterval (30362898604 / 1000000000000) (30362898606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3044945319705423 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28423488775 / 1000000000000) (28423505661 / 1000000000000), orderedInterval (-5348009148 / 1000000000000) (-5347992262 / 1000000000000)))) (orderedInterval (4190687777 / 1000000000000) (4190691769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2538557956062687 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23221063797 / 1000000000000) (23221063798 / 1000000000000), orderedInterval (21520101287 / 1000000000000) (21520101288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2242892940920427 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25015827375 / 1000000000000) (25015841355 / 1000000000000), orderedInterval (-22595809049 / 1000000000000) (-22595795070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (650077795230273 / 800000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8004031505 / 1000000000000) (8004031507 / 1000000000000), orderedInterval (-26826070832 / 1000000000000) (-26826070829 / 1000000000000)))) (orderedInterval (-236286200 / 1000000000000) (-236283851 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate568_chunkChecks4_2 :
    compactCertificate568.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1798149393326931 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33095683988 / 1000000000000) (-33095683987 / 1000000000000), orderedInterval (-17875246874 / 1000000000000) (-17875246873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1524311154682491 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40354835212 / 1000000000000) (-40354833491 / 1000000000000), orderedInterval (6538541598 / 1000000000000) (6538543319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (953843144564073 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24071134577 / 1000000000000) (24071134578 / 1000000000000), orderedInterval (45669196345 / 1000000000000) (45669196346 / 1000000000000)))) (orderedInterval (7164687842 / 1000000000000) (7164687990 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (512980015485591 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-15659333335 / 1000000000000) (-15659333334 / 1000000000000), orderedInterval (-68633267932 / 1000000000000) (-68633267931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1392840530869773 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11750178796 / 1000000000000) (-11750178795 / 1000000000000), orderedInterval (-41095146717 / 1000000000000) (-41095146716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1901804667303021 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35115857047 / 1000000000000) (-35115846175 / 1000000000000), orderedInterval (10325591259 / 1000000000000) (10325602131 / 1000000000000)))) (orderedInterval (3790650323 / 1000000000000) (3790651520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (804156855435927 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (38851540951 / 1000000000000) (38851540952 / 1000000000000), orderedInterval (40612131837 / 1000000000000) (40612131838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3268852971893367 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25853007767 / 1000000000000) (25853007790 / 1000000000000), orderedInterval (10502495950 / 1000000000000) (10502495973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2183442293294553 / 4000000000000) 4 (IntervalRat.scale (879 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (294401226 / 1000000000000) (294401227 / 1000000000000), orderedInterval (34149136106 / 1000000000000) (34149136107 / 1000000000000)))) (orderedInterval (-25358384093 / 1000000000000) (-25358383445 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate568_chunkChecks4 :
    compactCertificate568.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate568.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate568_chunkChecks4_0
    compactCertificate568_chunkChecks4_1 compactCertificate568_chunkChecks4_2

theorem compactCertificate568_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate568.chunkCheck r b = true :=
  compactCertificate568.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate568_chunkChecks0
    · exact compactCertificate568_chunkChecks1
    · exact compactCertificate568_chunkChecks2
    · exact compactCertificate568_chunkChecks3
    · exact compactCertificate568_chunkChecks4)

theorem compactCertificate568_coefficient0 :
    compactCertificate568.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate568_coefficient1 :
    compactCertificate568.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate568_coefficient2 :
    compactCertificate568.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate568_coefficient3 :
    compactCertificate568.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate568_coefficient4 :
    compactCertificate568.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate568_coefficients : ∀ r : Fin 5,
    compactCertificate568.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate568_coefficient0
  · exact compactCertificate568_coefficient1
  · exact compactCertificate568_coefficient2
  · exact compactCertificate568_coefficient3
  · exact compactCertificate568_coefficient4

theorem compactCertificate568_lower : (1 : ℚ) ≤ compactCertificate568.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate568, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate568_proves {t : ℝ} (ht : t ∈ compactCertificate568.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate568.proves compactCertificate568_states compactCertificate568_chunks
    compactCertificate568_coefficients compactCertificate568_lower ht

end Erdos232
