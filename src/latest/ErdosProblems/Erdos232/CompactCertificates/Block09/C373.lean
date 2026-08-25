/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate373 : CompactCertificate where
  left := 244
  right := 245
  center := 489 / 2
  grid := fun i =>
    match i.val with
    | 0 => 78
    | 1 => 57
    | 2 => 93
    | 3 => 17
    | 4 => 45
    | 5 => 122
    | 6 => 90
    | 7 => 154
    | 8 => 113
    | 9 => 174
    | 10 => 101
    | 11 => 178
    | 12 => 167
    | 13 => 119
    | 14 => 135
    | 15 => 112
    | 16 => 99
    | 17 => 144
    | 18 => 80
    | 19 => 68
    | 20 => 42
    | 21 => 23
    | 22 => 62
    | 23 => 84
    | 24 => 36
    | 25 => 145
    | _ => 97
  point := fun i =>
    match i.val with
    | 0 => 489 / 2
    | 1 => 720390373523589 / 4000000000000
    | 2 => 232959445443237 / 800000000000
    | 3 => 210208114315023 / 4000000000000
    | 4 => 564648563267331 / 4000000000000
    | 5 => 1533130689059127 / 4000000000000
    | 6 => 1129297126535151 / 4000000000000
    | 7 => 1935069874570923 / 4000000000000
    | 8 => 1425363711385857 / 4000000000000
    | 9 => 2186874481994511 / 4000000000000
    | 10 => 1262592570863319 / 4000000000000
    | 11 => 2240492673379971 / 4000000000000
    | 12 => 2093358884537199 / 4000000000000
    | 13 => 1493919676555167 / 4000000000000
    | 14 => 1693945689801993 / 4000000000000
    | 15 => 1412235313441017 / 4000000000000
    | 16 => 1247752728225357 / 4000000000000
    | 17 => 361647374138343 / 800000000000
    | 18 => 1000335669325221 / 4000000000000
    | 19 => 847995625301181 / 4000000000000
    | 20 => 530636288614143 / 4000000000000
    | 21 => 285377960833281 / 4000000000000
    | 22 => 774856677582843 / 4000000000000
    | 23 => 1058000548704411 / 4000000000000
    | 24 => 447363711385857 / 4000000000000
    | 25 => 1818508649892897 / 4000000000000
    | _ => 1214679501047823 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (12161962782 / 1000000000000) (12161962783 / 1000000000000), orderedInterval (49531696058 / 1000000000000) (49531696059 / 1000000000000))
    | 1 => (orderedInterval (-57740296889 / 1000000000000) (-57740295525 / 1000000000000), orderedInterval (14334435059 / 1000000000000) (14334436423 / 1000000000000))
    | 2 => (orderedInterval (8547478342 / 1000000000000) (8547478368 / 1000000000000), orderedInterval (-45983612540 / 1000000000000) (-45983612514 / 1000000000000))
    | 3 => (orderedInterval (7920495132 / 1000000000000) (7920495160 / 1000000000000), orderedInterval (-109856468897 / 1000000000000) (-109856468868 / 1000000000000))
    | 4 => (orderedInterval (-36520431735 / 1000000000000) (-36520431734 / 1000000000000), orderedInterval (-56227698427 / 1000000000000) (-56227698426 / 1000000000000))
    | 5 => (orderedInterval (29048928271 / 1000000000000) (29048928272 / 1000000000000), orderedInterval (28547529547 / 1000000000000) (28547529548 / 1000000000000))
    | 6 => (orderedInterval (16989931244 / 1000000000000) (16989931245 / 1000000000000), orderedInterval (44312540021 / 1000000000000) (44312540022 / 1000000000000))
    | 7 => (orderedInterval (24656556466 / 1000000000000) (24656556467 / 1000000000000), orderedInterval (26583097860 / 1000000000000) (26583097861 / 1000000000000))
    | 8 => (orderedInterval (-35918582262 / 1000000000000) (-35918507417 / 1000000000000), orderedInterval (22330489584 / 1000000000000) (22330564430 / 1000000000000))
    | 9 => (orderedInterval (26008391605 / 1000000000000) (26008391606 / 1000000000000), orderedInterval (22066962998 / 1000000000000) (22066962999 / 1000000000000))
    | 10 => (orderedInterval (34259281770 / 1000000000000) (34259340009 / 1000000000000), orderedInterval (-29091589484 / 1000000000000) (-29091531245 / 1000000000000))
    | 11 => (orderedInterval (33410591179 / 1000000000000) (33410594736 / 1000000000000), orderedInterval (-4535697662 / 1000000000000) (-4535694104 / 1000000000000))
    | 12 => (orderedInterval (17363110156 / 1000000000000) (17363110693 / 1000000000000), orderedInterval (-30265204357 / 1000000000000) (-30265203820 / 1000000000000))
    | 13 => (orderedInterval (-16663489313 / 1000000000000) (-16663489312 / 1000000000000), orderedInterval (-37751907789 / 1000000000000) (-37751907788 / 1000000000000))
    | 14 => (orderedInterval (-6043765674 / 1000000000000) (-6043765673 / 1000000000000), orderedInterval (-38291121405 / 1000000000000) (-38291121404 / 1000000000000))
    | 15 => (orderedInterval (38864229994 / 1000000000000) (38864250906 / 1000000000000), orderedInterval (-17164243187 / 1000000000000) (-17164222274 / 1000000000000))
    | 16 => (orderedInterval (-44766484476 / 1000000000000) (-44766483621 / 1000000000000), orderedInterval (6139021770 / 1000000000000) (6139022625 / 1000000000000))
    | 17 => (orderedInterval (16491548006 / 1000000000000) (16491548007 / 1000000000000), orderedInterval (33690744943 / 1000000000000) (33690744944 / 1000000000000))
    | 18 => (orderedInterval (-22335549182 / 1000000000000) (-22335547842 / 1000000000000), orderedInterval (45285687129 / 1000000000000) (45285688469 / 1000000000000))
    | 19 => (orderedInterval (-40973029158 / 1000000000000) (-40972954206 / 1000000000000), orderedInterval (36485492065 / 1000000000000) (36485567017 / 1000000000000))
    | 20 => (orderedInterval (69083559941 / 1000000000000) (69083559954 / 1000000000000), orderedInterval (4872288679 / 1000000000000) (4872288693 / 1000000000000))
    | 21 => (orderedInterval (12104404945 / 1000000000000) (12104405003 / 1000000000000), orderedInterval (-93769808662 / 1000000000000) (-93769808604 / 1000000000000))
    | 22 => (orderedInterval (-15832825431 / 1000000000000) (-15832825225 / 1000000000000), orderedInterval (55138217632 / 1000000000000) (55138217838 / 1000000000000))
    | 23 => (orderedInterval (48271521544 / 1000000000000) (48271521551 / 1000000000000), orderedInterval (8668600304 / 1000000000000) (8668600311 / 1000000000000))
    | 24 => (orderedInterval (-34311567007 / 1000000000000) (-34311563604 / 1000000000000), orderedInterval (67346689038 / 1000000000000) (67346692441 / 1000000000000))
    | 25 => (orderedInterval (4429525227 / 1000000000000) (4429525230 / 1000000000000), orderedInterval (-37162534497 / 1000000000000) (-37162534494 / 1000000000000))
    | _ => (orderedInterval (12636924813 / 1000000000000) (12636924909 / 1000000000000), orderedInterval (-44029114248 / 1000000000000) (-44029114153 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (4784124507 / 1000000000000) (4784124539 / 1000000000000)
      | 1 => orderedInterval (-3484434381 / 1000000000000) (-3484434351 / 1000000000000)
      | 2 => orderedInterval (-1628588125 / 1000000000000) (-1628586302 / 1000000000000)
      | 3 => orderedInterval (2666466039 / 1000000000000) (2666470957 / 1000000000000)
      | 4 => orderedInterval (-1858620117 / 1000000000000) (-1858620077 / 1000000000000)
      | 5 => orderedInterval (3432877160 / 1000000000000) (3432877474 / 1000000000000)
      | 6 => orderedInterval (8139386678 / 1000000000000) (8139391197 / 1000000000000)
      | 7 => orderedInterval (-3563787013 / 1000000000000) (-3563786977 / 1000000000000)
      | _ => orderedInterval (-2938434972 / 1000000000000) (-2938434865 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16517259268 / 1000000000000) (16517259300 / 1000000000000)
      | 1 => orderedInterval (-4110485394 / 1000000000000) (-4110485360 / 1000000000000)
      | 2 => orderedInterval (-835761038 / 1000000000000) (-835758378 / 1000000000000)
      | 3 => orderedInterval (-13027479504 / 1000000000000) (-13027472573 / 1000000000000)
      | 4 => orderedInterval (-3948028569 / 1000000000000) (-3948028500 / 1000000000000)
      | 5 => orderedInterval (860474471 / 1000000000000) (860474917 / 1000000000000)
      | 6 => orderedInterval (-9110716885 / 1000000000000) (-9110712930 / 1000000000000)
      | 7 => orderedInterval (-1204539256 / 1000000000000) (-1204539225 / 1000000000000)
      | _ => orderedInterval (16070850325 / 1000000000000) (16070850453 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5307687162 / 1000000000000) (-5307687130 / 1000000000000)
      | 1 => orderedInterval (5540034912 / 1000000000000) (5540034959 / 1000000000000)
      | 2 => orderedInterval (4824573840 / 1000000000000) (4824577736 / 1000000000000)
      | 3 => orderedInterval (-5996725377 / 1000000000000) (-5996715073 / 1000000000000)
      | 4 => orderedInterval (5037249320 / 1000000000000) (5037249444 / 1000000000000)
      | 5 => orderedInterval (-6552713923 / 1000000000000) (-6552713287 / 1000000000000)
      | 6 => orderedInterval (-6104598005 / 1000000000000) (-6104594520 / 1000000000000)
      | 7 => orderedInterval (4127946897 / 1000000000000) (4127946928 / 1000000000000)
      | _ => orderedInterval (4881673351 / 1000000000000) (4881673525 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15105379653 / 1000000000000) (-15105379619 / 1000000000000)
      | 1 => orderedInterval (8178535126 / 1000000000000) (8178535196 / 1000000000000)
      | 2 => orderedInterval (4660652995 / 1000000000000) (4660658689 / 1000000000000)
      | 3 => orderedInterval (56252721982 / 1000000000000) (56252738333 / 1000000000000)
      | 4 => orderedInterval (6338392608 / 1000000000000) (6338392836 / 1000000000000)
      | 5 => orderedInterval (-4098963180 / 1000000000000) (-4098962271 / 1000000000000)
      | 6 => orderedInterval (9094008405 / 1000000000000) (9094011466 / 1000000000000)
      | 7 => orderedInterval (1403282117 / 1000000000000) (1403282148 / 1000000000000)
      | _ => orderedInterval (-35333428547 / 1000000000000) (-35333428293 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (5794872414 / 1000000000000) (5794872451 / 1000000000000)
      | 1 => orderedInterval (-12686046810 / 1000000000000) (-12686046703 / 1000000000000)
      | 2 => orderedInterval (-15610221649 / 1000000000000) (-15610213299 / 1000000000000)
      | 3 => orderedInterval (21874308579 / 1000000000000) (21874336718 / 1000000000000)
      | 4 => orderedInterval (-14935149960 / 1000000000000) (-14935149525 / 1000000000000)
      | 5 => orderedInterval (13706593779 / 1000000000000) (13706595090 / 1000000000000)
      | 6 => orderedInterval (5340083357 / 1000000000000) (5340086066 / 1000000000000)
      | 7 => orderedInterval (-4938230865 / 1000000000000) (-4938230834 / 1000000000000)
      | _ => orderedInterval (-9672067926 / 1000000000000) (-9672067531 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (5548989776 / 1000000000000) (5549001595 / 1000000000000)
    | 1 => orderedInterval (1211573418 / 1000000000000) (1211587704 / 1000000000000)
    | 2 => orderedInterval (449753853 / 1000000000000) (449772582 / 1000000000000)
    | 3 => orderedInterval (31389821853 / 1000000000000) (31389848485 / 1000000000000)
    | _ => orderedInterval (-11125859081 / 1000000000000) (-11125817567 / 1000000000000)

theorem compactCertificate373_stateChecks0 :
    compactCertificate373.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (489 / 2)) (orderedInterval (12161962782 / 1000000000000) (12161962783 / 1000000000000), orderedInterval (49531696058 / 1000000000000) (49531696059 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (720390373523589 / 4000000000000)) (orderedInterval (-57740296889 / 1000000000000) (-57740295525 / 1000000000000), orderedInterval (14334435059 / 1000000000000) (14334436423 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (232959445443237 / 800000000000)) (orderedInterval (8547478342 / 1000000000000) (8547478368 / 1000000000000), orderedInterval (-45983612540 / 1000000000000) (-45983612514 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_stateChecks1 :
    compactCertificate373.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (210208114315023 / 4000000000000)) (orderedInterval (7920495132 / 1000000000000) (7920495160 / 1000000000000), orderedInterval (-109856468897 / 1000000000000) (-109856468868 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (564648563267331 / 4000000000000)) (orderedInterval (-36520431735 / 1000000000000) (-36520431734 / 1000000000000), orderedInterval (-56227698427 / 1000000000000) (-56227698426 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1533130689059127 / 4000000000000)) (orderedInterval (29048928271 / 1000000000000) (29048928272 / 1000000000000), orderedInterval (28547529547 / 1000000000000) (28547529548 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_stateChecks2 :
    compactCertificate373.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1129297126535151 / 4000000000000)) (orderedInterval (16989931244 / 1000000000000) (16989931245 / 1000000000000), orderedInterval (44312540021 / 1000000000000) (44312540022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1935069874570923 / 4000000000000)) (orderedInterval (24656556466 / 1000000000000) (24656556467 / 1000000000000), orderedInterval (26583097860 / 1000000000000) (26583097861 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1425363711385857 / 4000000000000)) (orderedInterval (-35918582262 / 1000000000000) (-35918507417 / 1000000000000), orderedInterval (22330489584 / 1000000000000) (22330564430 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_stateChecks3 :
    compactCertificate373.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2186874481994511 / 4000000000000)) (orderedInterval (26008391605 / 1000000000000) (26008391606 / 1000000000000), orderedInterval (22066962998 / 1000000000000) (22066962999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1262592570863319 / 4000000000000)) (orderedInterval (34259281770 / 1000000000000) (34259340009 / 1000000000000), orderedInterval (-29091589484 / 1000000000000) (-29091531245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2240492673379971 / 4000000000000)) (orderedInterval (33410591179 / 1000000000000) (33410594736 / 1000000000000), orderedInterval (-4535697662 / 1000000000000) (-4535694104 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_stateChecks4 :
    compactCertificate373.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2093358884537199 / 4000000000000)) (orderedInterval (17363110156 / 1000000000000) (17363110693 / 1000000000000), orderedInterval (-30265204357 / 1000000000000) (-30265203820 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1493919676555167 / 4000000000000)) (orderedInterval (-16663489313 / 1000000000000) (-16663489312 / 1000000000000), orderedInterval (-37751907789 / 1000000000000) (-37751907788 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1693945689801993 / 4000000000000)) (orderedInterval (-6043765674 / 1000000000000) (-6043765673 / 1000000000000), orderedInterval (-38291121405 / 1000000000000) (-38291121404 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_stateChecks5 :
    compactCertificate373.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1412235313441017 / 4000000000000)) (orderedInterval (38864229994 / 1000000000000) (38864250906 / 1000000000000), orderedInterval (-17164243187 / 1000000000000) (-17164222274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1247752728225357 / 4000000000000)) (orderedInterval (-44766484476 / 1000000000000) (-44766483621 / 1000000000000), orderedInterval (6139021770 / 1000000000000) (6139022625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (361647374138343 / 800000000000)) (orderedInterval (16491548006 / 1000000000000) (16491548007 / 1000000000000), orderedInterval (33690744943 / 1000000000000) (33690744944 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_stateChecks6 :
    compactCertificate373.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1000335669325221 / 4000000000000)) (orderedInterval (-22335549182 / 1000000000000) (-22335547842 / 1000000000000), orderedInterval (45285687129 / 1000000000000) (45285688469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (847995625301181 / 4000000000000)) (orderedInterval (-40973029158 / 1000000000000) (-40972954206 / 1000000000000), orderedInterval (36485492065 / 1000000000000) (36485567017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (530636288614143 / 4000000000000)) (orderedInterval (69083559941 / 1000000000000) (69083559954 / 1000000000000), orderedInterval (4872288679 / 1000000000000) (4872288693 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_stateChecks7 :
    compactCertificate373.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (285377960833281 / 4000000000000)) (orderedInterval (12104404945 / 1000000000000) (12104405003 / 1000000000000), orderedInterval (-93769808662 / 1000000000000) (-93769808604 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (774856677582843 / 4000000000000)) (orderedInterval (-15832825431 / 1000000000000) (-15832825225 / 1000000000000), orderedInterval (55138217632 / 1000000000000) (55138217838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1058000548704411 / 4000000000000)) (orderedInterval (48271521544 / 1000000000000) (48271521551 / 1000000000000), orderedInterval (8668600304 / 1000000000000) (8668600311 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_stateChecks8 :
    compactCertificate373.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (447363711385857 / 4000000000000)) (orderedInterval (-34311567007 / 1000000000000) (-34311563604 / 1000000000000), orderedInterval (67346689038 / 1000000000000) (67346692441 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1818508649892897 / 4000000000000)) (orderedInterval (4429525227 / 1000000000000) (4429525230 / 1000000000000), orderedInterval (-37162534497 / 1000000000000) (-37162534494 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1214679501047823 / 4000000000000)) (orderedInterval (12636924813 / 1000000000000) (12636924909 / 1000000000000), orderedInterval (-44029114248 / 1000000000000) (-44029114153 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_states : ∀ j,
    BesselStateValid (compactCertificate373.point j) (compactCertificate373.state j) :=
  compactCertificate373.statesValid_of_checks3 compactCertificate373_stateChecks0
    compactCertificate373_stateChecks1 compactCertificate373_stateChecks2
    compactCertificate373_stateChecks3 compactCertificate373_stateChecks4
    compactCertificate373_stateChecks5 compactCertificate373_stateChecks6
    compactCertificate373_stateChecks7 compactCertificate373_stateChecks8

theorem compactCertificate373_chunkChecks0_0 :
    compactCertificate373.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (489 / 2) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12161962782 / 1000000000000) (12161962783 / 1000000000000), orderedInterval (49531696058 / 1000000000000) (49531696059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (720390373523589 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57740296889 / 1000000000000) (-57740295525 / 1000000000000), orderedInterval (14334435059 / 1000000000000) (14334436423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (232959445443237 / 800000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8547478342 / 1000000000000) (8547478368 / 1000000000000), orderedInterval (-45983612540 / 1000000000000) (-45983612514 / 1000000000000)))) (orderedInterval (4784124507 / 1000000000000) (4784124539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (210208114315023 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7920495132 / 1000000000000) (7920495160 / 1000000000000), orderedInterval (-109856468897 / 1000000000000) (-109856468868 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (564648563267331 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36520431735 / 1000000000000) (-36520431734 / 1000000000000), orderedInterval (-56227698427 / 1000000000000) (-56227698426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1533130689059127 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29048928271 / 1000000000000) (29048928272 / 1000000000000), orderedInterval (28547529547 / 1000000000000) (28547529548 / 1000000000000)))) (orderedInterval (-3484434381 / 1000000000000) (-3484434351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1129297126535151 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16989931244 / 1000000000000) (16989931245 / 1000000000000), orderedInterval (44312540021 / 1000000000000) (44312540022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1935069874570923 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24656556466 / 1000000000000) (24656556467 / 1000000000000), orderedInterval (26583097860 / 1000000000000) (26583097861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1425363711385857 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35918582262 / 1000000000000) (-35918507417 / 1000000000000), orderedInterval (22330489584 / 1000000000000) (22330564430 / 1000000000000)))) (orderedInterval (-1628588125 / 1000000000000) (-1628586302 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks0_1 :
    compactCertificate373.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2186874481994511 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26008391605 / 1000000000000) (26008391606 / 1000000000000), orderedInterval (22066962998 / 1000000000000) (22066962999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1262592570863319 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34259281770 / 1000000000000) (34259340009 / 1000000000000), orderedInterval (-29091589484 / 1000000000000) (-29091531245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2240492673379971 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33410591179 / 1000000000000) (33410594736 / 1000000000000), orderedInterval (-4535697662 / 1000000000000) (-4535694104 / 1000000000000)))) (orderedInterval (2666466039 / 1000000000000) (2666470957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2093358884537199 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17363110156 / 1000000000000) (17363110693 / 1000000000000), orderedInterval (-30265204357 / 1000000000000) (-30265203820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1493919676555167 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16663489313 / 1000000000000) (-16663489312 / 1000000000000), orderedInterval (-37751907789 / 1000000000000) (-37751907788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1693945689801993 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6043765674 / 1000000000000) (-6043765673 / 1000000000000), orderedInterval (-38291121405 / 1000000000000) (-38291121404 / 1000000000000)))) (orderedInterval (-1858620117 / 1000000000000) (-1858620077 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1412235313441017 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38864229994 / 1000000000000) (38864250906 / 1000000000000), orderedInterval (-17164243187 / 1000000000000) (-17164222274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1247752728225357 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44766484476 / 1000000000000) (-44766483621 / 1000000000000), orderedInterval (6139021770 / 1000000000000) (6139022625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (361647374138343 / 800000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16491548006 / 1000000000000) (16491548007 / 1000000000000), orderedInterval (33690744943 / 1000000000000) (33690744944 / 1000000000000)))) (orderedInterval (3432877160 / 1000000000000) (3432877474 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks0_2 :
    compactCertificate373.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1000335669325221 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-22335549182 / 1000000000000) (-22335547842 / 1000000000000), orderedInterval (45285687129 / 1000000000000) (45285688469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (847995625301181 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40973029158 / 1000000000000) (-40972954206 / 1000000000000), orderedInterval (36485492065 / 1000000000000) (36485567017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (530636288614143 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69083559941 / 1000000000000) (69083559954 / 1000000000000), orderedInterval (4872288679 / 1000000000000) (4872288693 / 1000000000000)))) (orderedInterval (8139386678 / 1000000000000) (8139391197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (285377960833281 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12104404945 / 1000000000000) (12104405003 / 1000000000000), orderedInterval (-93769808662 / 1000000000000) (-93769808604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (774856677582843 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15832825431 / 1000000000000) (-15832825225 / 1000000000000), orderedInterval (55138217632 / 1000000000000) (55138217838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1058000548704411 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48271521544 / 1000000000000) (48271521551 / 1000000000000), orderedInterval (8668600304 / 1000000000000) (8668600311 / 1000000000000)))) (orderedInterval (-3563787013 / 1000000000000) (-3563786977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (447363711385857 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34311567007 / 1000000000000) (-34311563604 / 1000000000000), orderedInterval (67346689038 / 1000000000000) (67346692441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1818508649892897 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4429525227 / 1000000000000) (4429525230 / 1000000000000), orderedInterval (-37162534497 / 1000000000000) (-37162534494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1214679501047823 / 4000000000000) 0 (IntervalRat.scale (489 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12636924813 / 1000000000000) (12636924909 / 1000000000000), orderedInterval (-44029114248 / 1000000000000) (-44029114153 / 1000000000000)))) (orderedInterval (-2938434972 / 1000000000000) (-2938434865 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks0 :
    compactCertificate373.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate373.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate373_chunkChecks0_0
    compactCertificate373_chunkChecks0_1 compactCertificate373_chunkChecks0_2

theorem compactCertificate373_chunkChecks1_0 :
    compactCertificate373.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (489 / 2) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12161962782 / 1000000000000) (12161962783 / 1000000000000), orderedInterval (49531696058 / 1000000000000) (49531696059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (720390373523589 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57740296889 / 1000000000000) (-57740295525 / 1000000000000), orderedInterval (14334435059 / 1000000000000) (14334436423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (232959445443237 / 800000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8547478342 / 1000000000000) (8547478368 / 1000000000000), orderedInterval (-45983612540 / 1000000000000) (-45983612514 / 1000000000000)))) (orderedInterval (16517259268 / 1000000000000) (16517259300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (210208114315023 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7920495132 / 1000000000000) (7920495160 / 1000000000000), orderedInterval (-109856468897 / 1000000000000) (-109856468868 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (564648563267331 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36520431735 / 1000000000000) (-36520431734 / 1000000000000), orderedInterval (-56227698427 / 1000000000000) (-56227698426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1533130689059127 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29048928271 / 1000000000000) (29048928272 / 1000000000000), orderedInterval (28547529547 / 1000000000000) (28547529548 / 1000000000000)))) (orderedInterval (-4110485394 / 1000000000000) (-4110485360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1129297126535151 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16989931244 / 1000000000000) (16989931245 / 1000000000000), orderedInterval (44312540021 / 1000000000000) (44312540022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1935069874570923 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24656556466 / 1000000000000) (24656556467 / 1000000000000), orderedInterval (26583097860 / 1000000000000) (26583097861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1425363711385857 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35918582262 / 1000000000000) (-35918507417 / 1000000000000), orderedInterval (22330489584 / 1000000000000) (22330564430 / 1000000000000)))) (orderedInterval (-835761038 / 1000000000000) (-835758378 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks1_1 :
    compactCertificate373.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2186874481994511 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26008391605 / 1000000000000) (26008391606 / 1000000000000), orderedInterval (22066962998 / 1000000000000) (22066962999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1262592570863319 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34259281770 / 1000000000000) (34259340009 / 1000000000000), orderedInterval (-29091589484 / 1000000000000) (-29091531245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2240492673379971 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33410591179 / 1000000000000) (33410594736 / 1000000000000), orderedInterval (-4535697662 / 1000000000000) (-4535694104 / 1000000000000)))) (orderedInterval (-13027479504 / 1000000000000) (-13027472573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2093358884537199 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17363110156 / 1000000000000) (17363110693 / 1000000000000), orderedInterval (-30265204357 / 1000000000000) (-30265203820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1493919676555167 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16663489313 / 1000000000000) (-16663489312 / 1000000000000), orderedInterval (-37751907789 / 1000000000000) (-37751907788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1693945689801993 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6043765674 / 1000000000000) (-6043765673 / 1000000000000), orderedInterval (-38291121405 / 1000000000000) (-38291121404 / 1000000000000)))) (orderedInterval (-3948028569 / 1000000000000) (-3948028500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1412235313441017 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38864229994 / 1000000000000) (38864250906 / 1000000000000), orderedInterval (-17164243187 / 1000000000000) (-17164222274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1247752728225357 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44766484476 / 1000000000000) (-44766483621 / 1000000000000), orderedInterval (6139021770 / 1000000000000) (6139022625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (361647374138343 / 800000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16491548006 / 1000000000000) (16491548007 / 1000000000000), orderedInterval (33690744943 / 1000000000000) (33690744944 / 1000000000000)))) (orderedInterval (860474471 / 1000000000000) (860474917 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks1_2 :
    compactCertificate373.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1000335669325221 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-22335549182 / 1000000000000) (-22335547842 / 1000000000000), orderedInterval (45285687129 / 1000000000000) (45285688469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (847995625301181 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40973029158 / 1000000000000) (-40972954206 / 1000000000000), orderedInterval (36485492065 / 1000000000000) (36485567017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (530636288614143 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69083559941 / 1000000000000) (69083559954 / 1000000000000), orderedInterval (4872288679 / 1000000000000) (4872288693 / 1000000000000)))) (orderedInterval (-9110716885 / 1000000000000) (-9110712930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (285377960833281 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12104404945 / 1000000000000) (12104405003 / 1000000000000), orderedInterval (-93769808662 / 1000000000000) (-93769808604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (774856677582843 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15832825431 / 1000000000000) (-15832825225 / 1000000000000), orderedInterval (55138217632 / 1000000000000) (55138217838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1058000548704411 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48271521544 / 1000000000000) (48271521551 / 1000000000000), orderedInterval (8668600304 / 1000000000000) (8668600311 / 1000000000000)))) (orderedInterval (-1204539256 / 1000000000000) (-1204539225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (447363711385857 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34311567007 / 1000000000000) (-34311563604 / 1000000000000), orderedInterval (67346689038 / 1000000000000) (67346692441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1818508649892897 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4429525227 / 1000000000000) (4429525230 / 1000000000000), orderedInterval (-37162534497 / 1000000000000) (-37162534494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1214679501047823 / 4000000000000) 1 (IntervalRat.scale (489 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12636924813 / 1000000000000) (12636924909 / 1000000000000), orderedInterval (-44029114248 / 1000000000000) (-44029114153 / 1000000000000)))) (orderedInterval (16070850325 / 1000000000000) (16070850453 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks1 :
    compactCertificate373.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate373.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate373_chunkChecks1_0
    compactCertificate373_chunkChecks1_1 compactCertificate373_chunkChecks1_2

theorem compactCertificate373_chunkChecks2_0 :
    compactCertificate373.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (489 / 2) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12161962782 / 1000000000000) (12161962783 / 1000000000000), orderedInterval (49531696058 / 1000000000000) (49531696059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (720390373523589 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57740296889 / 1000000000000) (-57740295525 / 1000000000000), orderedInterval (14334435059 / 1000000000000) (14334436423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (232959445443237 / 800000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8547478342 / 1000000000000) (8547478368 / 1000000000000), orderedInterval (-45983612540 / 1000000000000) (-45983612514 / 1000000000000)))) (orderedInterval (-5307687162 / 1000000000000) (-5307687130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (210208114315023 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7920495132 / 1000000000000) (7920495160 / 1000000000000), orderedInterval (-109856468897 / 1000000000000) (-109856468868 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (564648563267331 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36520431735 / 1000000000000) (-36520431734 / 1000000000000), orderedInterval (-56227698427 / 1000000000000) (-56227698426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1533130689059127 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29048928271 / 1000000000000) (29048928272 / 1000000000000), orderedInterval (28547529547 / 1000000000000) (28547529548 / 1000000000000)))) (orderedInterval (5540034912 / 1000000000000) (5540034959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1129297126535151 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16989931244 / 1000000000000) (16989931245 / 1000000000000), orderedInterval (44312540021 / 1000000000000) (44312540022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1935069874570923 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24656556466 / 1000000000000) (24656556467 / 1000000000000), orderedInterval (26583097860 / 1000000000000) (26583097861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1425363711385857 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35918582262 / 1000000000000) (-35918507417 / 1000000000000), orderedInterval (22330489584 / 1000000000000) (22330564430 / 1000000000000)))) (orderedInterval (4824573840 / 1000000000000) (4824577736 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks2_1 :
    compactCertificate373.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2186874481994511 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26008391605 / 1000000000000) (26008391606 / 1000000000000), orderedInterval (22066962998 / 1000000000000) (22066962999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1262592570863319 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34259281770 / 1000000000000) (34259340009 / 1000000000000), orderedInterval (-29091589484 / 1000000000000) (-29091531245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2240492673379971 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33410591179 / 1000000000000) (33410594736 / 1000000000000), orderedInterval (-4535697662 / 1000000000000) (-4535694104 / 1000000000000)))) (orderedInterval (-5996725377 / 1000000000000) (-5996715073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2093358884537199 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17363110156 / 1000000000000) (17363110693 / 1000000000000), orderedInterval (-30265204357 / 1000000000000) (-30265203820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1493919676555167 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16663489313 / 1000000000000) (-16663489312 / 1000000000000), orderedInterval (-37751907789 / 1000000000000) (-37751907788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1693945689801993 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6043765674 / 1000000000000) (-6043765673 / 1000000000000), orderedInterval (-38291121405 / 1000000000000) (-38291121404 / 1000000000000)))) (orderedInterval (5037249320 / 1000000000000) (5037249444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1412235313441017 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38864229994 / 1000000000000) (38864250906 / 1000000000000), orderedInterval (-17164243187 / 1000000000000) (-17164222274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1247752728225357 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44766484476 / 1000000000000) (-44766483621 / 1000000000000), orderedInterval (6139021770 / 1000000000000) (6139022625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (361647374138343 / 800000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16491548006 / 1000000000000) (16491548007 / 1000000000000), orderedInterval (33690744943 / 1000000000000) (33690744944 / 1000000000000)))) (orderedInterval (-6552713923 / 1000000000000) (-6552713287 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks2_2 :
    compactCertificate373.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1000335669325221 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-22335549182 / 1000000000000) (-22335547842 / 1000000000000), orderedInterval (45285687129 / 1000000000000) (45285688469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (847995625301181 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40973029158 / 1000000000000) (-40972954206 / 1000000000000), orderedInterval (36485492065 / 1000000000000) (36485567017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (530636288614143 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69083559941 / 1000000000000) (69083559954 / 1000000000000), orderedInterval (4872288679 / 1000000000000) (4872288693 / 1000000000000)))) (orderedInterval (-6104598005 / 1000000000000) (-6104594520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (285377960833281 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12104404945 / 1000000000000) (12104405003 / 1000000000000), orderedInterval (-93769808662 / 1000000000000) (-93769808604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (774856677582843 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15832825431 / 1000000000000) (-15832825225 / 1000000000000), orderedInterval (55138217632 / 1000000000000) (55138217838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1058000548704411 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48271521544 / 1000000000000) (48271521551 / 1000000000000), orderedInterval (8668600304 / 1000000000000) (8668600311 / 1000000000000)))) (orderedInterval (4127946897 / 1000000000000) (4127946928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (447363711385857 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34311567007 / 1000000000000) (-34311563604 / 1000000000000), orderedInterval (67346689038 / 1000000000000) (67346692441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1818508649892897 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4429525227 / 1000000000000) (4429525230 / 1000000000000), orderedInterval (-37162534497 / 1000000000000) (-37162534494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1214679501047823 / 4000000000000) 2 (IntervalRat.scale (489 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12636924813 / 1000000000000) (12636924909 / 1000000000000), orderedInterval (-44029114248 / 1000000000000) (-44029114153 / 1000000000000)))) (orderedInterval (4881673351 / 1000000000000) (4881673525 / 1000000000000))) = true
  rfl'

theorem compactCertificate373_chunkChecks2 :
    compactCertificate373.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate373.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate373_chunkChecks2_0
    compactCertificate373_chunkChecks2_1 compactCertificate373_chunkChecks2_2

theorem compactCertificate373_chunkChecks3_0 :
    compactCertificate373.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (489 / 2) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12161962782 / 1000000000000) (12161962783 / 1000000000000), orderedInterval (49531696058 / 1000000000000) (49531696059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (720390373523589 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57740296889 / 1000000000000) (-57740295525 / 1000000000000), orderedInterval (14334435059 / 1000000000000) (14334436423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (232959445443237 / 800000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8547478342 / 1000000000000) (8547478368 / 1000000000000), orderedInterval (-45983612540 / 1000000000000) (-45983612514 / 1000000000000)))) (orderedInterval (-15105379653 / 1000000000000) (-15105379619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (210208114315023 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7920495132 / 1000000000000) (7920495160 / 1000000000000), orderedInterval (-109856468897 / 1000000000000) (-109856468868 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (564648563267331 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36520431735 / 1000000000000) (-36520431734 / 1000000000000), orderedInterval (-56227698427 / 1000000000000) (-56227698426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1533130689059127 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29048928271 / 1000000000000) (29048928272 / 1000000000000), orderedInterval (28547529547 / 1000000000000) (28547529548 / 1000000000000)))) (orderedInterval (8178535126 / 1000000000000) (8178535196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1129297126535151 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16989931244 / 1000000000000) (16989931245 / 1000000000000), orderedInterval (44312540021 / 1000000000000) (44312540022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1935069874570923 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24656556466 / 1000000000000) (24656556467 / 1000000000000), orderedInterval (26583097860 / 1000000000000) (26583097861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1425363711385857 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35918582262 / 1000000000000) (-35918507417 / 1000000000000), orderedInterval (22330489584 / 1000000000000) (22330564430 / 1000000000000)))) (orderedInterval (4660652995 / 1000000000000) (4660658689 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate373_chunkChecks3_1 :
    compactCertificate373.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2186874481994511 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26008391605 / 1000000000000) (26008391606 / 1000000000000), orderedInterval (22066962998 / 1000000000000) (22066962999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1262592570863319 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34259281770 / 1000000000000) (34259340009 / 1000000000000), orderedInterval (-29091589484 / 1000000000000) (-29091531245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2240492673379971 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33410591179 / 1000000000000) (33410594736 / 1000000000000), orderedInterval (-4535697662 / 1000000000000) (-4535694104 / 1000000000000)))) (orderedInterval (56252721982 / 1000000000000) (56252738333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2093358884537199 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17363110156 / 1000000000000) (17363110693 / 1000000000000), orderedInterval (-30265204357 / 1000000000000) (-30265203820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1493919676555167 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16663489313 / 1000000000000) (-16663489312 / 1000000000000), orderedInterval (-37751907789 / 1000000000000) (-37751907788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1693945689801993 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6043765674 / 1000000000000) (-6043765673 / 1000000000000), orderedInterval (-38291121405 / 1000000000000) (-38291121404 / 1000000000000)))) (orderedInterval (6338392608 / 1000000000000) (6338392836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1412235313441017 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38864229994 / 1000000000000) (38864250906 / 1000000000000), orderedInterval (-17164243187 / 1000000000000) (-17164222274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1247752728225357 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44766484476 / 1000000000000) (-44766483621 / 1000000000000), orderedInterval (6139021770 / 1000000000000) (6139022625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (361647374138343 / 800000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16491548006 / 1000000000000) (16491548007 / 1000000000000), orderedInterval (33690744943 / 1000000000000) (33690744944 / 1000000000000)))) (orderedInterval (-4098963180 / 1000000000000) (-4098962271 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate373_chunkChecks3_2 :
    compactCertificate373.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1000335669325221 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-22335549182 / 1000000000000) (-22335547842 / 1000000000000), orderedInterval (45285687129 / 1000000000000) (45285688469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (847995625301181 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40973029158 / 1000000000000) (-40972954206 / 1000000000000), orderedInterval (36485492065 / 1000000000000) (36485567017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (530636288614143 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69083559941 / 1000000000000) (69083559954 / 1000000000000), orderedInterval (4872288679 / 1000000000000) (4872288693 / 1000000000000)))) (orderedInterval (9094008405 / 1000000000000) (9094011466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (285377960833281 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12104404945 / 1000000000000) (12104405003 / 1000000000000), orderedInterval (-93769808662 / 1000000000000) (-93769808604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (774856677582843 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15832825431 / 1000000000000) (-15832825225 / 1000000000000), orderedInterval (55138217632 / 1000000000000) (55138217838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1058000548704411 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48271521544 / 1000000000000) (48271521551 / 1000000000000), orderedInterval (8668600304 / 1000000000000) (8668600311 / 1000000000000)))) (orderedInterval (1403282117 / 1000000000000) (1403282148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (447363711385857 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34311567007 / 1000000000000) (-34311563604 / 1000000000000), orderedInterval (67346689038 / 1000000000000) (67346692441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1818508649892897 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4429525227 / 1000000000000) (4429525230 / 1000000000000), orderedInterval (-37162534497 / 1000000000000) (-37162534494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1214679501047823 / 4000000000000) 3 (IntervalRat.scale (489 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12636924813 / 1000000000000) (12636924909 / 1000000000000), orderedInterval (-44029114248 / 1000000000000) (-44029114153 / 1000000000000)))) (orderedInterval (-35333428547 / 1000000000000) (-35333428293 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate373_chunkChecks3 :
    compactCertificate373.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate373.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate373_chunkChecks3_0
    compactCertificate373_chunkChecks3_1 compactCertificate373_chunkChecks3_2

theorem compactCertificate373_chunkChecks4_0 :
    compactCertificate373.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (489 / 2) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12161962782 / 1000000000000) (12161962783 / 1000000000000), orderedInterval (49531696058 / 1000000000000) (49531696059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (720390373523589 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57740296889 / 1000000000000) (-57740295525 / 1000000000000), orderedInterval (14334435059 / 1000000000000) (14334436423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (232959445443237 / 800000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8547478342 / 1000000000000) (8547478368 / 1000000000000), orderedInterval (-45983612540 / 1000000000000) (-45983612514 / 1000000000000)))) (orderedInterval (5794872414 / 1000000000000) (5794872451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (210208114315023 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (7920495132 / 1000000000000) (7920495160 / 1000000000000), orderedInterval (-109856468897 / 1000000000000) (-109856468868 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (564648563267331 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36520431735 / 1000000000000) (-36520431734 / 1000000000000), orderedInterval (-56227698427 / 1000000000000) (-56227698426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1533130689059127 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29048928271 / 1000000000000) (29048928272 / 1000000000000), orderedInterval (28547529547 / 1000000000000) (28547529548 / 1000000000000)))) (orderedInterval (-12686046810 / 1000000000000) (-12686046703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1129297126535151 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16989931244 / 1000000000000) (16989931245 / 1000000000000), orderedInterval (44312540021 / 1000000000000) (44312540022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1935069874570923 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24656556466 / 1000000000000) (24656556467 / 1000000000000), orderedInterval (26583097860 / 1000000000000) (26583097861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1425363711385857 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35918582262 / 1000000000000) (-35918507417 / 1000000000000), orderedInterval (22330489584 / 1000000000000) (22330564430 / 1000000000000)))) (orderedInterval (-15610221649 / 1000000000000) (-15610213299 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate373_chunkChecks4_1 :
    compactCertificate373.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2186874481994511 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26008391605 / 1000000000000) (26008391606 / 1000000000000), orderedInterval (22066962998 / 1000000000000) (22066962999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1262592570863319 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34259281770 / 1000000000000) (34259340009 / 1000000000000), orderedInterval (-29091589484 / 1000000000000) (-29091531245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2240492673379971 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33410591179 / 1000000000000) (33410594736 / 1000000000000), orderedInterval (-4535697662 / 1000000000000) (-4535694104 / 1000000000000)))) (orderedInterval (21874308579 / 1000000000000) (21874336718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2093358884537199 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17363110156 / 1000000000000) (17363110693 / 1000000000000), orderedInterval (-30265204357 / 1000000000000) (-30265203820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1493919676555167 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16663489313 / 1000000000000) (-16663489312 / 1000000000000), orderedInterval (-37751907789 / 1000000000000) (-37751907788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1693945689801993 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6043765674 / 1000000000000) (-6043765673 / 1000000000000), orderedInterval (-38291121405 / 1000000000000) (-38291121404 / 1000000000000)))) (orderedInterval (-14935149960 / 1000000000000) (-14935149525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1412235313441017 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38864229994 / 1000000000000) (38864250906 / 1000000000000), orderedInterval (-17164243187 / 1000000000000) (-17164222274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1247752728225357 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-44766484476 / 1000000000000) (-44766483621 / 1000000000000), orderedInterval (6139021770 / 1000000000000) (6139022625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (361647374138343 / 800000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16491548006 / 1000000000000) (16491548007 / 1000000000000), orderedInterval (33690744943 / 1000000000000) (33690744944 / 1000000000000)))) (orderedInterval (13706593779 / 1000000000000) (13706595090 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate373_chunkChecks4_2 :
    compactCertificate373.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1000335669325221 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-22335549182 / 1000000000000) (-22335547842 / 1000000000000), orderedInterval (45285687129 / 1000000000000) (45285688469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (847995625301181 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40973029158 / 1000000000000) (-40972954206 / 1000000000000), orderedInterval (36485492065 / 1000000000000) (36485567017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (530636288614143 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (69083559941 / 1000000000000) (69083559954 / 1000000000000), orderedInterval (4872288679 / 1000000000000) (4872288693 / 1000000000000)))) (orderedInterval (5340083357 / 1000000000000) (5340086066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (285377960833281 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12104404945 / 1000000000000) (12104405003 / 1000000000000), orderedInterval (-93769808662 / 1000000000000) (-93769808604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (774856677582843 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15832825431 / 1000000000000) (-15832825225 / 1000000000000), orderedInterval (55138217632 / 1000000000000) (55138217838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1058000548704411 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48271521544 / 1000000000000) (48271521551 / 1000000000000), orderedInterval (8668600304 / 1000000000000) (8668600311 / 1000000000000)))) (orderedInterval (-4938230865 / 1000000000000) (-4938230834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (447363711385857 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-34311567007 / 1000000000000) (-34311563604 / 1000000000000), orderedInterval (67346689038 / 1000000000000) (67346692441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1818508649892897 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4429525227 / 1000000000000) (4429525230 / 1000000000000), orderedInterval (-37162534497 / 1000000000000) (-37162534494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1214679501047823 / 4000000000000) 4 (IntervalRat.scale (489 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12636924813 / 1000000000000) (12636924909 / 1000000000000), orderedInterval (-44029114248 / 1000000000000) (-44029114153 / 1000000000000)))) (orderedInterval (-9672067926 / 1000000000000) (-9672067531 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate373_chunkChecks4 :
    compactCertificate373.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate373.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate373_chunkChecks4_0
    compactCertificate373_chunkChecks4_1 compactCertificate373_chunkChecks4_2

theorem compactCertificate373_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate373.chunkCheck r b = true :=
  compactCertificate373.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate373_chunkChecks0
    · exact compactCertificate373_chunkChecks1
    · exact compactCertificate373_chunkChecks2
    · exact compactCertificate373_chunkChecks3
    · exact compactCertificate373_chunkChecks4)

theorem compactCertificate373_coefficient0 :
    compactCertificate373.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate373_coefficient1 :
    compactCertificate373.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate373_coefficient2 :
    compactCertificate373.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate373_coefficient3 :
    compactCertificate373.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate373_coefficient4 :
    compactCertificate373.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate373_coefficients : ∀ r : Fin 5,
    compactCertificate373.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate373_coefficient0
  · exact compactCertificate373_coefficient1
  · exact compactCertificate373_coefficient2
  · exact compactCertificate373_coefficient3
  · exact compactCertificate373_coefficient4

theorem compactCertificate373_lower : (1 : ℚ) ≤ compactCertificate373.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate373, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate373_proves {t : ℝ} (ht : t ∈ compactCertificate373.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate373.proves compactCertificate373_states compactCertificate373_chunks
    compactCertificate373_coefficients compactCertificate373_lower ht

end Erdos232
